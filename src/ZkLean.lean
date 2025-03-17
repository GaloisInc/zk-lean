-- This module serves as the root of the `ZkLean` library.
-- Import modules here that should be built as part of the library.

import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable


class JoltField (f: Type) extends Field f, BEq f, Inhabited f, Witnessable f (ZKExpr f)
