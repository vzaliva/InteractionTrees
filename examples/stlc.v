From Coq Require Import
     Arith List.
Import ListNotations.

From ExtLib.Structures Require Import
     Monad.
Import MonadNotation.
Open Scope monad_scope.

From ITree Require Import
     ITree
     OpenSum
     Fix.

(* Warm-up exercise. Denotational semantics of STLC. *)
Module Stlc.

Inductive ty : Type :=
| B : ty
| Arrow : ty -> ty -> ty
.

Infix "->" := Arrow : ty_scope.
Bind Scope ty_scope with ty.

Definition context : Type := list ty.

Inductive var (u : ty) : context -> Type :=
| Here  g   : var u (u :: g)
| There g v : var u g -> var u (v :: g)
.

Arguments Here {u g}.
Arguments There {u g v}.

Inductive tm (g : context) : ty -> Type :=
| Var u : var u g -> tm g u
| App u v : tm g (u -> v) -> tm g u -> tm g v
| Lam u v : tm (u :: g) v -> tm g (u -> v)
.

Arguments Var {g u}.
Arguments App {g u v}.
Arguments Lam {g u v}.

Fixpoint ty_sem (A : Type) (u : ty) : Type :=
  match u with
  | B => A
  | Arrow v w => (ty_sem A v -> ty_sem A w)
  end.

Fixpoint context_sem (A : Type) (g : context) : Type :=
  match g with
  | [] => unit
  | u :: g' => ty_sem A u * context_sem A g'
  end.

Fixpoint var_sem (A : Type) {g : context} {u : ty} (x : var u g) :
  context_sem A g -> ty_sem A u :=
  match x with
  | Here => fun r => fst r
  | There x' => fun r => var_sem A x' (snd r)
  end.

Fixpoint tm_sem (A : Type) {g : context} {u : ty} (t : tm g u) :
  context_sem A g -> ty_sem A u :=
  match t with
  | Var x => var_sem A x
  | App t1 t2 =>
    fun r => (tm_sem A t1 r) (tm_sem A t2 r)
  | Lam t1 =>
    fun r e => tm_sem A t1 (e, r)
  end.

Definition sem (A : Type) {u : ty} (t : tm [] u) : ty_sem A u :=
  tm_sem A t tt.

End Stlc.

(* STLC with fix *)
Module StlcFix.

Inductive ty : Type :=
| B : ty
| Arrow : ty -> ty -> ty
.

Bind Scope ty_scope with ty.
Delimit Scope ty_scope with ty.

Infix "->" := Arrow : ty_scope.

Definition context : Type := list ty.

Inductive var (u : ty) : context -> Type :=
| Here  g   : var u (u :: g)
| There g v : var u g -> var u (v :: g)
.

Arguments Here {u g}.
Arguments There {u g v}.

Inductive tm (g : context) : ty -> Type :=
| Var u : var u g -> tm g u
| App u v : tm g (u -> v) -> tm g u -> tm g v
| Lam u v : tm (u :: g) v -> tm g (u -> v)
| Fix u v : tm (u :: (u -> v)%ty :: g) v -> tm g (u -> v)
.

Arguments Var {g u}.
Arguments App {g u v}.
Arguments Lam {g u v}.
Arguments Fix {g u v}.

End StlcFix.

Module StlcFixFuel.

Import StlcFix.

Class MonadFix (M : Type -> Type) `{Monad M} : Type :=
  fixm : forall A B, ((A -> M B) -> A -> M B) -> A -> M B.

Arguments fixm {M _ _ A B}.

Fixpoint ty_sem (M : Type -> Type) (A : Type) (u : ty) : Type :=
  match u with
  | B => A
  | Arrow v w => (ty_sem M A v -> M (ty_sem M A w))
  end.

Fixpoint context_sem (M : Type -> Type) (A : Type) (g : context) : Type :=
  match g with
  | [] => unit
  | u :: g' => ty_sem M A u * context_sem M A g'
  end.

Fixpoint var_sem (M : Type -> Type) (A : Type)
         {g : context} {u : ty} (x : var u g) :
  context_sem M A g -> ty_sem M A u :=
  match x with
  | Here => fun r => fst r
  | There x' => fun r => var_sem M A x' (snd r)
  end.

Fixpoint tm_sem (M : Type -> Type) `{MonadFix M} (A : Type)
         {g : context} {u : ty} (t : tm g u) :
  context_sem M A g -> M (ty_sem M A u) :=
  match t with
  | Var x => fun g => ret (var_sem M A x g)
  | App t1 t2 =>
    fun r =>
      s <- tm_sem M A t2 r;;
      f <- tm_sem M A t1 r;;
      f s
  | Lam t1 =>
    fun r =>
      ret (fun e => tm_sem M A t1 (e, r))
  | Fix t1 =>
    fun r =>
      ret (fixm (fun self e =>
                   tm_sem M A t1 (e, (self, r))))
  end.

Definition sem (M : Type -> Type) `{MonadFix M}
           (A : Type) {u : ty} (t : tm [] u) : M (ty_sem M A u) :=
  tm_sem M A t tt.

End StlcFixFuel.

Module StlcFixITreeVersion0.

Import StlcFix.

Notation "E ~> F" := (forall X, E X -> F X) (at level 90) : type_scope.

Fixpoint ty_sem (E : Type -> Type) (A : Type) (u : ty) : Type :=
  match u with
  | B => A
  | Arrow v w => (ty_sem E A v -> itree E (ty_sem E A w))
  end.

Fixpoint context_sem (E : Type -> Type) (A : Type) (g : context) : Type :=
  match g with
  | [] => unit
  | u :: g' => ty_sem E A u * context_sem E A g'
  end.

Fixpoint var_sem (E : Type -> Type) (A : Type)
         {g : context} {u : ty} (x : var u g) :
  context_sem E A g -> ty_sem E A u :=
  match x with
  | Here => fun r => fst r
  | There x' => fun r => var_sem E A x' (snd r)
  end.

Module Fail1.

Fixpoint tm_sem (E : Type -> Type) (A : Type)
         {g : context} {u : ty} (t : tm g u) :
  context_sem E A g -> itree E (ty_sem E A u) :=
  match t with
  | Var x => fun g => ret (var_sem E A x g)
  | App t1 t2 =>
    fun r =>
      s <- tm_sem E A t2 r;;
      f <- tm_sem E A t1 r;;
      f s
  | Lam t1 =>
    fun r =>
      ret (fun e => tm_sem E A t1 (e, r))
  | Fix t1 =>
    fun r => spin (* DUMMY *)
  end.

(* We need to modify [E] to insert fix, so this suggests replacing
   the context t with [forall F, {E ~> F} -> context_sem F A g]. *)

Definition sem (E : Type -> Type)
           (A : Type) {u : ty} (t : tm [] u) : itree E (ty_sem E A u) :=
  tm_sem E A t tt.

End Fail1.

Module Fail2.

Parameter BAD_ty_sem_map :
  forall A u E F, (E ~> F) -> ty_sem E A u -> ty_sem F A u.

Fixpoint tm_sem (E : Type -> Type) (A : Type)
         {g : context} {u : ty} (t : tm g u) :
  (forall F, (E ~> F) -> context_sem F A g) -> itree E (ty_sem E A u) :=
  match t with
  | Var x => fun g => ret (var_sem E A x (g _ (fun _ x => x)))
  | App t1 t2 =>
    fun r =>
      s <- tm_sem E A t2 r;;
      f <- tm_sem E A t1 r;;
      f s
  | Lam t1 =>
    fun r =>
      ret (fun e => tm_sem E A t1 (fun F inF =>
             (BAD_ty_sem_map _ _ _ F inF e, r F inF)))
  | Fix t1 =>
    fun r => spin (* DUMMY *)
  end.

(* We are already stuck in the [Lam] case, trying to define
   [BAD_ty_sem_map]. It is undefinable: [E] has negative occurences
   in [ty_sem E A u].

   We will have a similar problem in [Fix]: note the inner [E] in
   [itree E (ty_sem E A u)], so after the recursive call we need to
   define
   [itree (E + fixE) (ty_sem (E + fixE) A u)
          -> itree E (ty_sem E A u)], which is also impossible.

   Maybe we can do more generalization in [ty_sem] like we already
   did with the context. This seems tricky.
 *)

End Fail2.

End StlcFixITreeVersion0.

Module Untyped.

Inductive term : Type :=
| Var : nat -> term
(* DeBruijn indexed *)

| App : term -> term -> term

| Lam : term -> term
.

Inductive headvar : Type :=
| VVar : nat -> headvar
| VApp : headvar -> value -> headvar
with value : Type :=
| VHead : headvar -> value
| VLam : term -> value
.

Fixpoint to_term (v : value) : term :=
  match v with
  | VHead hv => hv_to_term hv
  | VLam t => Lam t
  end
with hv_to_term (hv : headvar) : term :=
  match hv with
  | VVar n => Var n
  | VApp hv v => App (hv_to_term hv) (to_term v)
  end.

Fixpoint shift (n m : nat) (s : term) :=
  match s with
  | Var p =>
    if p <? m then Var (n + p)
    else Var p
  | App t1 t2 => App (shift n m t1) (shift n m t2)
  | Lam t => Lam (shift n (S m) t)
  end.

Fixpoint subst (n : nat) (s t : term) :=
  match t with
  | Var m =>
    if m <? n then Var m
    else if m =? n then shift n O s
    else Var (pred m)
  | App t1 t2 => App (subst n s t1) (subst n s t2)
  | Lam t => Lam (subst (S n) s t)
  end.

(* big-step call-by-value *)
Definition big_step : term -> itree emptyE value :=
  mfix (fun _ => value)
       (fun _ lift big_step t =>
    match t with
    | Var n => ret (VHead (VVar n))
    | App t1 t2 =>
      t2' <- big_step t2;;
      t1' <- big_step t1;;
      match t1' with
      | VHead hv => ret (VHead (VApp hv t2'))
      | VLam t1'' =>
        big_step (subst O (to_term t2') t1'')
      end
    | Lam t => ret (VLam t)
    end).

End Untyped.
