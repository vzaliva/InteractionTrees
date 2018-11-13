From ITree Require Import
     ITree Fix Equivalence.

(* To make this provable:
   - use eutt instead of eq
   - require parametricity of [body] or rewrite RHS using [interp] *)
Theorem mfix0_unfold E codom (body : fix_body0 E codom) :
  mfix0 body = body _ (fun _ t => t) (mfix0 body).
Proof.
Admitted.

Theorem mfix1_unfold E dom codom (body : fix_body1 E dom codom) :
  mfix1 body = body _ (fun _ t => t) (mfix1 body).
Proof.
Admitted.
