Require Import Pretty.

Extraction Language Haskell.
Require Import ExtrHaskellBasic ExtrHaskellNatInteger.

Extract Inductive Ascii.ascii => "Prelude.Char"
[
"{- If this appears, you're using Ascii internals. Please don't -}
 __"
]
"{- If this appears, you're using Ascii internals. Please don't -}
 __".

Extract Inductive String.string => "(([]) Prelude.Char)" [ "[]" "(:)" ].
Extract Inlined Constant String.length => "((Prelude..) Prelude.toInteger Prelude.length)".
Extract Inlined Constant String.append => "(Prelude.++)".

Extract Inlined Constant Nat.ltb => "(Prelude.<)".

Extraction "Pretty.hs" examples.tree.testtree.
