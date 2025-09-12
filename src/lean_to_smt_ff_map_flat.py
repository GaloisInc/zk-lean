#!/usr/bin/env python3
# lean_to_smt_ff_map_flat.py
#
# Flat FF SMT generator from Lean subtable + explicit mapping (no x vectors).
# - Balanced parsing of `subtableFromMLE (fun x => BODY)`.
# - General MLE parser: +, -, *, parentheses, integers, x[NN], unary/binary minus.
# - Reads BV↔FF mapping lines:
#     some (bool_to_bv[_W] bvK[i]) = map_f_to_bv[_W] fvG[j] [->]
# - Reads output line:
#     some <bvout> = map_f_to_bv[_W] foutput [->]
#   to get real output BV name and exact width W.
# - Declares fvGroup_idx bits, ties them to BV extracts, enforces bitness b(b-1)=0.
# - Builds poly_inputs from MLE AST (replacing x[i] by fvGroup_idx according to
#   Vector.append fv1 fv2, or --append-order fv1,fv2 if missing).
# - Builds poly_bvout from bvout’s bits as Σ 2^i * out_i (mod p).
# - Asserts: foutput = poly_bvout and foutput = poly_inputs.
# - If exactly 2 BV inputs, also asserts (= bvout (bvand a b)).
#
# Usage:
#   python3 lean_to_smt_ff_map_flat.py --prime 18446744073709551557 file.lean -o outdir
#   python3 lean_to_smt_ff_map_flat.py --prime P dir --append-order fv1,fv2 -o outdir
#
import os, re, sys, math, argparse, pathlib

# ---------- Lean def header ----------
DEF_PAT = re.compile(
    r"def\s+(?P<name>[A-Za-z0-9_']+)\s*\[Field\s+f\]\s*:\s*Subtable\s+f\s+(?P<N>\d+)\s*:=",
    re.MULTILINE
)

# ---------- BV↔FF mapping ----------
MAP_PAT = re.compile(
    r"""some\s*\(\s*bool_to_bv(?:_\d+)?\s+
        (?P<bv>[A-Za-z_][A-Za-z0-9_]*)\s*\[\s*(?P<bidx>\d+)\s*\]\s*\)\s*=\s*
        map_f_to_bv(?:_\d+)?\s+(?P<fv>[A-Za-z_][A-Za-z0-9_]*)\s*\[\s*(?P<fidx>\d+)\s*\]
        (?:\s*->)?""",
    re.MULTILINE | re.VERBOSE
)

# Output mapping: some <bvout> = map_f_to_bv[_W] foutput [->]
OUT_PAT = re.compile(
    r"""some\s+
        (?P<bvout>[A-Za-z_][A-Za-z0-9_]*)\s*=\s*
        map_f_to_bv(?:_(?P<w>\d+))?\s+
        foutput
        (?:\s*->)?""",
    re.MULTILINE | re.VERBOSE,
)

# Vector.append fv1 fv2 (to infer x-index grouping)
APPEND_PAT = re.compile(r"Vector\.append\s+([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_]*)")

# ---------- Balanced extraction of MLE BODY ----------
def _find_matching_paren(s: str, open_pos: int) -> int:
    assert s[open_pos] == '(', "internal: not at '('"
    bal = 1
    i = open_pos + 1
    while i < len(s):
        c = s[i]
        if c == '(':
            bal += 1
        elif c == ')':
            bal -= 1
            if bal == 0:
                return i
        i += 1
    return -1

def _extract_mle_body_around(text: str, start_idx: int):
    """
    From after 'def ... :=', find subtableFromMLE (fun x => BODY) and return BODY.
    """
    kw = "subtableFromMLE"
    k = text.find(kw, start_idx)
    if k < 0:
        return None, start_idx
    p = text.find('(', k)
    if p < 0:
        return None, k + len(kw)
    q = _find_matching_paren(text, p)
    if q < 0:
        raise ValueError("Unbalanced parentheses in subtableFromMLE call.")
    inner = text[p + 1 : q]
    # Look for "fun x =>" or "fun x=>"
    arrow = "fun x =>"
    a = inner.find(arrow)
    if a < 0:
        arrow2 = "fun x=>"
        a = inner.find(arrow2)
        if a < 0:
            raise ValueError("Could not find 'fun x =>' inside subtableFromMLE.")
        arrow = arrow2
    body = inner[a + len(arrow):].strip()
    return body, q + 1

def parse_defs(text: str):
    """
    Find defs and their balanced MLE bodies.
    """
    out = []
    pos = 0
    while True:
        m = DEF_PAT.search(text, pos)
        if not m:
            break
        name = m.group("name")
        N = int(m.group("N"))
        body, endpos = _extract_mle_body_around(text, m.end())
        if body is None:
            pos = m.end()
            continue
        out.append((name, N, body))
        pos = endpos
    return out

# ---------- Expression tokenizer & parser ----------
TOK_SPEC = [
    ("INT",   r"\d+"),
    ("X",     r"x\[\d+\]"),
    ("PLUS",  r"\+"),
    ("MUL",   r"\*"),
    ("LP",    r"\("),
    ("RP",    r"\)"),
    ("MINUS", r"-"),
    ("WS",    r"\s+"),
]
TOK_REGEX = re.compile("|".join(f"(?P<{k}>{v})" for k,v in TOK_SPEC))

class Tok:
    def __init__(self, kind, text):
        self.kind = kind; self.text = text
    def __repr__(self): return f"{self.kind}:{self.text}"

def lex(s):
    pos = 0; out = []
    while pos < len(s):
        m = TOK_REGEX.match(s, pos)
        if not m:
            raise ValueError(f"Lexer error at: {s[pos:pos+80]!r}")
        kind = m.lastgroup; text = m.group()
        if kind != "WS":
            out.append(Tok(kind, text))
        pos = m.end()
    return out

class Node: pass
class Int(Node):
    def __init__(self, n): self.n = n
class X(Node):
    def __init__(self, idx): self.idx = idx
class Add(Node):
    def __init__(self, a, b): self.a=a; self.b=b
class Sub(Node):
    def __init__(self, a, b): self.a=a; self.b=b
class Mul(Node):
    def __init__(self, a, b): self.a=a; self.b=b
class Neg(Node):
    def __init__(self, a): self.a=a

# Pratt-ish parser: unary -, then * left-assoc, then +/-
class Parser:
    def __init__(self, toks):
        self.toks = toks; self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def eat(self, kind=None):
        t = self.peek()
        if not t: raise ValueError("Unexpected end of input")
        if kind and t.kind != kind:
            raise ValueError(f"Expected {kind}, got {t.kind} ({t.text})")
        self.i += 1
        return t

    def parse(self):
        node = self.parse_expr()
        if self.peek() is not None:
            raise ValueError(f"Trailing tokens starting at {self.peek()}")
        return node

    # expr := term ( (PLUS|MINUS) term )*
    def parse_expr(self):
        node = self.parse_term()
        while True:
            t = self.peek()
            if t and t.kind in ("PLUS","MINUS"):
                self.eat()
                rhs = self.parse_term()
                node = Add(node, rhs) if t.kind=="PLUS" else Sub(node, rhs)
            else:
                break
        return node

    # term := factor ( MUL factor )*
    def parse_term(self):
        node = self.parse_factor()
        while True:
            t = self.peek()
            if t and t.kind == "MUL":
                self.eat("MUL")
                rhs = self.parse_factor()
                node = Mul(node, rhs)
            else:
                break
        return node

    # factor := INT | X | LP expr RP | MINUS factor
    def parse_factor(self):
        t = self.peek()
        if not t: raise ValueError("Unexpected end in factor")
        if t.kind == "INT":
            self.eat("INT"); return Int(int(t.text))
        if t.kind == "X":
            self.eat("X"); idx = int(t.text[2:-1]); return X(idx)
        if t.kind == "LP":
            self.eat("LP"); node = self.parse_expr(); self.eat("RP"); return node
        if t.kind == "MINUS":
            self.eat("MINUS"); return Neg(self.parse_factor())
        raise ValueError(f"Unexpected token in factor: {t}")

# ---------- Mapping & append helpers ----------
def gather_mapping(text):
    fv_bits = {}
    bv_vars = set()
    bv_width = {}
    for mm in MAP_PAT.finditer(text):
        bv  = mm.group("bv"); bix = int(mm.group("bidx"))
        fv  = mm.group("fv"); fix = int(mm.group("fidx"))
        fv_bits.setdefault(fv, {})[fix] = (bv, bix)
        bv_vars.add(bv)
        bv_width[bv] = max(bv_width.get(bv, 0), bix + 1)
    return fv_bits, sorted(bv_vars), bv_width

def detect_append_order(text, fallback):
    m = APPEND_PAT.search(text)
    if m: return [m.group(1), m.group(2)]
    return fallback[:] if fallback else None

def detect_output_mapping(text, fallback_width):
    m = OUT_PAT.search(text)
    if not m:
        return ("bvoutput", max(1, fallback_width))
    name = m.group("bvout")
    wstr = m.group("w")
    width = int(wstr) if wstr is not None else fallback_width
    return (name, max(1, width))

# ---------- SMT helpers ----------
def ff_const(k, F="F"): return f"(as ff{k} {F})"
def ff_add(a,b): return f"(ff.add {a} {b})"
def ff_mul(a,b): return f"(ff.mul {a} {b})"

def ff_sub(a,b,p,F="F"):
    # a - b == a + (p-1)*b
    return ff_add(a, ff_mul(ff_const((p-1)%p, F), b))

def fold_ff_add(ts, F="F"):
    if not ts: return ff_const(0,F)
    acc = ts[0]
    for t in ts[1:]:
        acc = ff_add(acc, t)
    return acc

def ast_to_ff(node, x_to_name, p, F="F"):
    if isinstance(node, Int):
        return ff_const(node.n % p, F)
    if isinstance(node, X):
        name = x_to_name(node.idx)
        if name is None:
            raise ValueError(f"x[{node.idx}] not mapped to any fv group")
        return name
    if isinstance(node, Add):
        return ff_add(ast_to_ff(node.a, x_to_name, p, F),
                      ast_to_ff(node.b, x_to_name, p, F))
    if isinstance(node, Sub):
        return ff_sub(ast_to_ff(node.a, x_to_name, p, F),
                      ast_to_ff(node.b, x_to_name, p, F), p, F)
    if isinstance(node, Mul):
        return ff_mul(ast_to_ff(node.a, x_to_name, p, F),
                      ast_to_ff(node.b, x_to_name, p, F))
    if isinstance(node, Neg):
        return ff_sub(ff_const(0,F), ast_to_ff(node.a, x_to_name, p, F), p, F)
    raise TypeError(f"Unknown AST node: {node}")

def infer_output_width_from_pows(body_text):
    # Heuristic for AND-like LUTs: pick width from max integer if it's a power of two
    try:
        ints = [int(m.group()) for m in re.finditer(r"\b\d+\b", body_text)]
        if not ints: return 1
        mx = max(ints)
        if mx <= 0: return 1
        return (int(math.log2(mx)) + 1) if (mx & (mx - 1) == 0) else 1
    except Exception:
        return 1

# ---------- Main SMT generation ----------
def gen_smt(name, N_hint, body_text, full_text, prime_str, append_cli=None):
    # Parse MLE body
    ast = Parser(lex(body_text)).parse()

    # Mapping
    fv_bits, bv_vars, bv_width = gather_mapping(full_text)
    if not fv_bits:
        raise ValueError("No mapping lines found (bool_to_bv* = map_f_to_bv*).")

    # Append order → map x[i] to (fvGroup, idx)
    fv_sizes = {fv: (max(idxs.keys())+1) for fv, idxs in fv_bits.items() if idxs}
    append_order = detect_append_order(full_text, append_cli.split(",") if append_cli else None)
    if not append_order:
        append_order = sorted(fv_bits.keys())

    offsets, cur = {}, 0
    for g in append_order:
        size = fv_sizes.get(g, 0)
        offsets[g] = cur
        cur += size

    def x_to_pair(k):
        for g in append_order:
            off = offsets[g]; size = fv_sizes.get(g,0)
            if off <= k < off+size:
                return (g, k - off)
        return None

    def x_to_name(k):
        pair = x_to_pair(k)
        if not pair: return None
        fv, idx = pair
        return f"{fv}_{idx}"

    # BV output name/width
    fallback_out_w = infer_output_width_from_pows(body_text)
    if fallback_out_w < 1: fallback_out_w = 1
    bvout_name, w_out = detect_output_mapping(full_text, fallback_out_w)

    # SMT preamble
    p = int(prime_str); F = "F"
    lines = []
    lines.append("(set-logic ALL)")
    lines.append("(set-option :incremental true)")
    lines.append("(set-option :produce-models true)")
    lines.append(f"(define-sort {F} () (_ FiniteField {p}))")
    lines.append("")

    # Declare BV inputs
    for bv in bv_vars:
        w = bv_width.get(bv, N_hint if N_hint>0 else 1)
        lines.append(f"(declare-fun {bv} () (_ BitVec {w}))")

    # Declare BV output with detected name/width
    lines.append(f"(declare-fun {bvout_name} () (_ BitVec {w_out}))")
    lines.append("")

    ff0 = ff_const(0,F); ff1 = ff_const(1,F); ffm1 = ff_const((p-1)%p, F)

    # Declare fvGroup_idx bits; connect to BV extracts; enforce bitness
    for fv, idxs in fv_bits.items():
        max_i = max(idxs.keys())
        for i in range(max_i+1):
            lines.append(f"(declare-fun {fv}_{i} () {F})")
            sel = f"sel_{fv}_{i}"
            lines.append(f"(declare-fun {sel} () Bool)")
            if i in idxs:
                bv, bit = idxs[i]
                lines.append(f"(assert (= {sel} (= ((_ extract {bit} {bit}) {bv}) #b1)))")
            else:
                # unmapped: default false selector
                lines.append(f"(assert (= {sel} false))")
            lines.append(f"(assert (= {fv}_{i} (ite {sel} {ff1} {ff0})))")
            lines.append(f"(assert (= {ff_mul(f'{fv}_{i}', ff_add(f'{fv}_{i}', ffm1))} {ff0}))")

    # Output bits from actual bvout
    out_bits = []
    for i in range(w_out):
        lines.append(f"(declare-fun out_{i} () {F})")
        sel = f"sel_out_{i}"
        lines.append(f"(declare-fun {sel} () Bool)")
        lines.append(f"(assert (= {sel} (= ((_ extract {i} {i}) {bvout_name}) #b1)))")
        lines.append(f"(assert (= out_{i} (ite {sel} {ff1} {ff0})))")
        lines.append(f"(assert (= {ff_mul(f'out_{i}', ff_add(f'out_{i}', ffm1))} {ff0}))")
        out_bits.append(f"out_{i}")

    lines.append(f"(declare-fun foutput () {F})")
    lines.append("")

    # Build field poly from AST (x[i] → fvGroup_idx)
    poly_inputs = ast_to_ff(ast, x_to_name, p, F)
    lines.append(f"(define-fun poly_inputs () {F} {poly_inputs})")

    # Build field value of bvout: Σ 2^i * out_i
    ff_terms_out = []
    for i in range(w_out):
        coeff = (1 << i) % p
        ff_terms_out.append(ff_mul(ff_const(coeff, F), f"out_{i}"))
    poly_bvout = fold_ff_add(ff_terms_out, F) if ff_terms_out else ff0
    lines.append(f"(define-fun poly_bvout () {F} {poly_bvout})")

    # Equate both to foutput (Lean lemma equates foutput to the BV value)
    lines.append(f"(assert (= foutput poly_bvout))")
    lines.append(f"(assert (= foutput poly_inputs))")

    # Convenience: if exactly two BV inputs present, assert bvout == bvand
    if len(bv_vars) == 2:
        a, b = bv_vars[0], bv_vars[1]
        lines.append(f"(assert (= {bvout_name} (bvand {a} {b})))")
    else:
        lines.append(f";; NOTE: found {len(bv_vars)} BV inputs; skipping (= {bvout_name} (bvand ...)).")

    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-model)")

    header = f";; Auto-generated (FF, flat) from Lean subtable: {name}\n"
    return header + "\n".join(lines) + "\n"

# ---------- Driver ----------
def convert_file(in_path, out_dir, prime_str, append_cli=None):
    with open(in_path, "r", encoding="utf-8") as f:
        txt = f.read()
    out_paths = []
    for (name, N, body) in parse_defs(txt):
        smt = gen_smt(name, N, body, txt, prime_str, append_cli)
        out_name = f"{pathlib.Path(in_path).stem}_{name}.smt2"
        out_path = os.path.join(out_dir, out_name)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(smt)
        out_paths.append(out_path)
    return out_paths

def main():
    ap = argparse.ArgumentParser(description="Flat FF SMT generator (balanced MLE parser, BV/FF mapping, real bvout name/width).")
    ap.add_argument("inputs", nargs="+", help="Lean files or directories to scan")
    ap.add_argument("-o", "--out", default="smt_out_ff_flat", help="Output directory")
    ap.add_argument("--prime", required=True, help="Prime p for (_ FiniteField p)")
    ap.add_argument("--append-order", default=None, help="Comma-separated fv groups order, e.g., 'fv1,fv2'")
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    files = []
    for pth in args.inputs:
        if os.path.isdir(pth):
            for root, _, fnames in os.walk(pth):
                for fn in fnames:
                    if fn.endswith(".lean"):
                        files.append(os.path.join(root, fn))
        elif pth.endswith(".lean"):
            files.append(pth)

    if not files:
        print("No .lean files found.", file=sys.stderr); sys.exit(1)

    generated = []
    for f in files:
        generated += convert_file(f, args.out, args.prime, append_cli=args.append_order)

    print("Generated:")
    for g in generated:
        print("  ", g)

if __name__ == "__main__":
    main()
