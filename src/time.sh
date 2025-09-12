#!/usr/bin/env bash
set -euo pipefail

# --- config ---
OUTFILE="lean_times.csv"
MAX_ERR_LINES=3   # how many lines of error to keep in CSV (compact)

# --- choose timer: prefer GNU time (gtime), fallback to BSD time -p ---
if command -v gtime >/dev/null 2>&1; then
  TIME_CMD=(gtime -f "%e %U %S")
  PARSE_MODE="gnu"
else
  TIME_CMD=(/usr/bin/time -p)
  PARSE_MODE="bsd"
fi

# # --- ensure we’re in a Lake project ---
# if [ ! -f "lakefile.lean" ] && [ ! -f "lakefile.toml" ]; then
#   echo "❌ Run this from your Lake project root (no lakefile found)." >&2
#   exit 1
# fi

# # --- prebuild once so deps are compiled (not counted later) ---
# echo "▶️  Prebuilding project once with 'lake build'..."
# lake build >/dev/null

echo "file,real_time,user_time,sys_time,status,error" > "$OUTFILE"

i=0
total=$(find . -type f -wholename '*/ZkLean/*.lean' | wc -l | tr -d ' ')

find . -type f -wholename '*/ZkLean/*.lean'| sort | while read -r f; do
  i=$((i+1))
  printf "⏱️  [%d/%d] %s\r" "$i" "$total" "$f" >&2

  if [ "$PARSE_MODE" = "gnu" ]; then
    OUTPUT=$( { lake env "${TIME_CMD[@]}" lean "$f" >/dev/null; } 2>&1 ) || true
    EXIT=$?
    TIMES_LINE=$(printf "%s\n" "$OUTPUT" | head -n1)
    ERR_LINES=$(printf "%s\n" "$OUTPUT" | tail -n +2 | head -n "$MAX_ERR_LINES" | tr '\n' ' ' | sed 's/"/'\''/g')
    REAL=$(awk '{print $1}' <<<"$TIMES_LINE")
    USER=$(awk '{print $2}' <<<"$TIMES_LINE")
    SYS=$(awk '{print $3}' <<<"$TIMES_LINE")
  else
    OUTPUT=$( { lake env "${TIME_CMD[@]}" lean "$f" >/dev/null; } 2>&1 ) || true
    EXIT=$?
    REAL=$(echo "$OUTPUT" | awk '/^real /{print $2}' | tail -n1)
    USER=$(echo "$OUTPUT" | awk '/^user /{print $2}' | tail -n1)
    SYS=$( echo "$OUTPUT" | awk '/^sys /{print $2}'  | tail -n1)
    ERR_LINES=$(printf "%s\n" "$OUTPUT" | grep -vE '^(real|user|sys) ' | head -n "$MAX_ERR_LINES" | tr '\n' ' ' | sed 's/"/'\''/g')
  fi

  STATUS="OK"
  if [ "$EXIT" -ne 0 ]; then STATUS="FAIL"; fi

  echo "\"$f\",$REAL,$USER,$SYS,$STATUS,\"$ERR_LINES\"" >> "$OUTFILE"
done

echo
echo "✅ Timing results saved to $OUTFILE"