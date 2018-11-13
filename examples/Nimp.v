(* A nondeterministic Imp *)

From Coq Require Import
     List Relations.

From Paco Require Import paco2.

From ITree Require Import
     ITree Equivalence Fix FixFacts.

Inductive com : Type :=
| loop : com -> com (* Nondeterministically, continue or stop. *)
| choose : com -> com -> com
| skip : com
| seq : com -> com -> com
.

(* note(LY): I think ExtLib put this level too high *)
Infix ";;" := seq (at level 100, right associativity) : com_scope.
Delimit Scope com_scope with com.
Open Scope com_scope.

Example one_loop : com := loop skip.
Example two_loops : com := loop (loop skip).
Example loop_choose : com := loop (choose skip skip).
Example choose_loop : com := choose (loop skip) skip.

(* Unlabeled small-step *)
Module Unlabeled.

Reserved Infix "-->" (at level 80, no associativity).

Inductive step : relation com :=
| step_loop_stop c :
    loop c --> skip
| step_loop_go c :
    loop c --> (c ;; loop c)
| step_choose_l c1 c2 :
    choose c1 c2 --> c1
| step_choose_r c1 c2 :
    choose c1 c2 --> c2
| step_seq_go c1 c1' c2 :
    c1 --> c2 ->
    (c1 ;; c2) --> (c1' ;; c2)
| step_seq_next c2 :
    (skip ;; c2) --> c2

where "x --> y" := (step x y).

CoInductive infinite_steps (c : com) : Type :=
| more c' : step c c' -> infinite_steps c' -> infinite_steps c.

Lemma infinite_simple_loop : infinite_steps one_loop.
Proof.
  cofix self.
  eapply more.
  { eapply step_loop_go. }
  eapply more.
  { eapply step_seq_next. }
  apply self.
Qed.

End Unlabeled.

Module Labeled.

Reserved Notation "s --> t" (at level 80, no associativity).
Reserved Notation "s ! b --> t" (at level 80, b at next level, no associativity).
Reserved Notation "s ? b --> t" (at level 80, b at next level, no associativity).

Variant label := tau | bit (b : bool).

Inductive step : label -> relation com :=
| step_loop_stop c :
    loop c ! true --> skip
| step_loop_go c :
    loop c ! false --> (c ;; loop c)
| step_choose_l c1 c2 :
    choose c1 c2 ! true --> c1
| step_choose_r c1 c2 :
    choose c1 c2 ! false --> c2
| step_seq_go b c1 c1' c2 :
    c1 ? b --> c2 ->
    (c1 ;; c2) ? b --> (c1' ;; c2)
| step_seq_next c2 :
    (skip ;; c2) --> c2

where "x --> y" := (step tau x y)
and  "x ! b --> y" := (step (bit b) x y)
and  "x ? b --> y" := (step b x y).

CoInductive infinite_steps (c : com) : Type :=
| more b c' : step b c c' -> infinite_steps c' -> infinite_steps c.

Lemma infinite_simple_loop : infinite_steps one_loop.
Proof.
  cofix self.
  eapply more.
  { eapply step_loop_go. }
  eapply more.
  { eapply step_seq_next. }
  apply self.
Qed.

End Labeled.

(* Set of traces semantics *)
Module Traces.
Import ListNotations.

Inductive dir := Left | Right.

Module Naive.

Definition trace : Type := list dir.

(* Sets of traces *)
Definition trace_set : Type := trace -> Prop.

(* One trace, the empty trace. *)
Definition empty_trace : trace_set :=
  fun tr => tr = [].

Definition one : dir -> trace_set :=
  fun d tr => tr = [d].

Definition seq : trace_set -> trace_set -> trace_set :=
  fun P1 P2 tr =>
    exists tr1 tr2, tr = tr1 ++ tr2 /\ P1 tr1 /\ P2 tr2.

Definition or : trace_set -> trace_set -> trace_set :=
  fun P1 P2 tr => P1 tr \/ P2 tr.

(* star P tr <->
   exists tr1 ... trn,
     (tr = tr1 ++ ... ++ trn) /\
     P tr1 /\ ... /\ P trn *)
Inductive star (P : trace_set) : trace_set :=
| star_0 : star P []
| star_1 tr1 tr2 : P tr1 -> star P tr2 -> star P (tr1 ++ tr2)
.

Fixpoint eval (c : com) : trace_set :=
  match c with
  | loop c' => seq (star (seq (one Right) (eval c'))) (one Left)
  | choose c1 c2 => or (eval c1) (eval c2)
  | skip => empty_trace
  | (c1 ;; c2) => seq (eval c1) (eval c2)
  end.

(* The problem with this definition is it only captures traces of
   complete but finite executions. *)

End Naive.

Module PrefixClosed.
(* To define "prefix closed sets of traces", one issue is that in
   [seq P1 P2] we have to be careful to append traces of [P2] only
   to "complete" traces of [P1]. So we need to enrich the type of
   traces. *)

(* Explicit marker for termination. *)
Inductive fin := Done | More.

Definition le_fin (f1 f2 : fin) : Prop :=
  match f1, f2 with
  | Done, More => False
  | _, _ => True
  end.

Delimit Scope fin_scope with fin.
Infix "<=" := le_fin : fin_scope.

Lemma Done_max f : (f <= Done)%fin.
Proof. destruct f; constructor. Qed.

Lemma More_min  f : (More <= f)%fin.
Proof. constructor. Qed.

Hint Resolve Done_max More_min.

Definition trace : Type := list dir * fin.

Inductive prefix : trace -> trace -> Prop :=
| prefix_cons d tr1 f1 tr2 f2 :
    prefix (tr1, f1) (tr2, f2) -> prefix (d :: tr1, f1) (d :: tr2, f2)
| prefix_nil f1 tr2 f2 :
    (f1 <= f2)%fin ->
    prefix (nil, f1) (tr2, f2)
.

Lemma prefix_trans tr0 tr1 tr2 :
  prefix tr0 tr1 -> prefix tr1 tr2 -> prefix tr0 tr2.
Proof.
Admitted.

Lemma le_fin_prefix tr f1 f2 : (f1 <= f2)%fin -> prefix (tr, f1) (tr, f2).
Proof.
  intros.
  induction tr; constructor; auto.
Qed.

Lemma prefix_app tr0 f0 tr1 tr2 f12 :
  prefix (tr0, f0) (tr1 ++ tr2, f12) ->
  prefix (tr0, f0) (tr1, More) \/
  exists tr0', tr0 = tr1 ++ tr0' /\ prefix (tr0', f0) (tr2, f12).
Proof.
Admitted.

Module Import Core.

(* Sets of traces *)
Definition trace_set : Type := trace -> Prop.

Definition empty : trace_set := fun _ => False.

Definition empty_trace : trace_set := fun tr =>
  exists f, tr = ([], f).

Definition one : dir -> trace_set := fun d tr =>
  prefix tr ([d], Done).

Variant seq (P1 P2 : trace_set) : trace_set :=
(* A trace of P1, complete or incomplete *)
| seq_first tr1 f1 : P1 (tr1, f1) -> seq P1 P2 (tr1, f1)
| seq_both tr1 tr2 f2 : P1 (tr1, Done) -> P2 (tr2, f2) -> seq P1 P2 (tr1 ++ tr2, f2)
.

Definition or (P1 P2 : trace_set) : trace_set :=
  fun tr => P1 tr \/ P2 tr.

Inductive star (P : trace_set) : trace_set :=
| star_end tr f : P (tr, f) -> star P (tr, f)
| star_continue tr1 tr2 f2 :
    P (tr1, Done) -> star P (tr2, f2) -> star P (tr1 ++ tr2, f2).

Definition prefix_closed (P : trace -> Prop) :=
  forall tr1 tr2, P tr2 -> prefix tr1 tr2 -> P tr1.

Lemma prefix_closed_empty : prefix_closed empty.
Proof. intros ? ? []. Qed.

Lemma prefix_closed_empty_trace : prefix_closed empty_trace.
Proof.
  intros tr1 tr2 [] Hprefix.
  subst; inversion Hprefix.
  eexists; auto.
Qed.

Lemma prefix_closed_one d : prefix_closed (one d).
Proof.
  intros tr1 tr2 Htr2 Hprefix.
  inversion Htr2; subst.
  - inversion Hprefix; subst.
    + inversion H1; subst.
      inversion H2; subst.
      constructor; constructor; auto.
    + constructor; auto.
  - inversion Hprefix.
    constructor; auto.
Qed.

Lemma prefix_closed_seq P1 P2
      (H1 : prefix_closed P1) (H2 : prefix_closed P2) :
  prefix_closed (seq P1 P2).
Proof.
  intros [tr1 f1] [tr2 f2] Htr2 Hprefix.
  inversion Htr2; subst.
  - eapply seq_first, H1; eauto.
  - apply prefix_app in Hprefix.
    destruct Hprefix as [Hprefix | [tr0' [L M]] ].
    + eapply seq_first, H1; eauto.
      eapply prefix_trans.
      * eassumption.
      * apply le_fin_prefix; auto.
    + subst.
      eapply seq_both; auto.
      eapply H2; eauto.
Qed.

Lemma prefix_closed_or P1 P2
      (H1 : prefix_closed P1) (H2 : prefix_closed P2) :
  prefix_closed (or P1 P2).
Proof.
  intros tr1 tr2 [|].
  - left; eapply H1; eauto.
  - right; eapply H2; eauto.
Qed.

Lemma prefix_closed_star P (H : prefix_closed P) :
  prefix_closed (star P).
Proof.
Admitted.

End Core.

(* Prefix-closed sets of traces. *)
Definition trace_set1 : Type :=
  { P : trace -> Prop
  | prefix_closed P }.

End PrefixClosed.

Module Coinductive.
(* TODO: Define [trace] as a coinductive type. *)
End Coinductive.

End Traces.

Module Tree.

Variant nd : Type -> Type :=
| Or : nd bool.

Definition or {R : Type} (t1 t2 : itree nd R) : itree nd R :=
  Vis Or (fun b : bool => if b then t1 else t2).

(* Flip a coin *)
Definition choice : itree nd bool := liftE Or.

Definition eval : com -> itree nd unit :=
  mfix1 (fun _ lift eval (c : com) =>
    match c with
    | loop c =>
      (* note: [or] is not allowed under [mfix]. *)
      (b <- lift _ choice;;
      if b then Ret tt else (eval c;; eval (loop c)))%itree
    | choose c1 c2 =>
      (b <- lift _ choice;;
      if b then eval c1 else eval c2)%itree
    | (t1 ;; t2)%com => (eval t1;; eval t2)%itree
    | skip => Ret tt
    end
  ).

(* [itree] semantics of [one_loop]. *)
Definition one_loop_tree : itree nd unit :=
  mfix0 (fun _ lift self  =>
    (* note: [or] is not allowed under [mfix]. *)
    b <- lift _ choice;;
    if b then
      Ret tt
    else
      self)%itree.

Lemma eval_one_loop : (eval one_loop ~ one_loop_tree)%eutt.
Proof.
  pcofix eval_one_loop.
  unfold one_loop_tree. rewrite mfix0_unfold.
  unfold eval. rewrite mfix1_unfold.
  simpl.
  (* Here I would like to avoid [match_bind] and instead reason
     compositionally about [bind], but the proof seems to rely on
     [choice] producing at least one visible effect. *)
  do 2 rewrite (match_bind choice); simpl.
  pfold. split.
  { apply and_iff.
    split; apply finite_taus_Vis.
  }
  intros t1' t2' Ht1' Ht2'.
  apply unalltaus_notau_id in Ht1'; [|constructor].
  apply unalltaus_notau_id in Ht2'; [|constructor].
  subst.
  constructor.
  intro b.
  do 2 rewrite (match_bind (Ret _)); simpl.
  destruct b; simpl.
  - left. pfold. apply Reflexive_eutt_. left.
    eapply paco2_mon.
    { eapply Reflexive_eutt. }
    { intros ? ? []. }
  - right.
    fold eval. fold one_loop_tree.
    unfold eval at 1.
    rewrite mfix1_unfold. rewrite (match_bind (Ret _)); simpl.
    apply eval_one_loop.
Qed.

End Tree.
