From Coq Require Import
     Relations Setoid Eqdep JMeq.

From ITree Require Import
     ITree Eq.UpToTaus.

Section Bisimilarity.

Context {E : Type -> Type} {R : Type}.

Definition steps (t : itree E R) (f : itreeF E R (itree E R)) : Prop :=
  exists t',
    untaus t t' /\ t'.(observe) = f.

Definition is_simulation (r : relation (itree E R)) : Prop :=
  forall t1 t2 : itree E R,
    r t1 t2 ->
    (forall a,
        steps t1 (RetF a) -> steps t2 (RetF a)) /\
    (forall X1 (e1 : E X1) k1,
        steps t1 (VisF e1 k1) ->
        exists X2 (e2 : E X2) k2,
          steps t2 (VisF e2 k2) /\
          eq_dep _ E _ e1 _ e2 /\
          (forall x1 x2, JMeq x1 x2 -> r (k1 x1) (k2 x2))).

Definition equiv {A B} (r1 r2 : A -> B -> Prop) :=
  forall a b, r1 a b <-> r2 a b.

Instance Symmetric_equiv {A B} : Symmetric (@equiv A B).
Proof. firstorder. Qed.

Lemma is_simulation_equiv (r1 r2 : relation (itree E R)) :
  equiv r1 r2 -> is_simulation r1 -> is_simulation r2.
Proof.
  intros er12 sim_1 t1 t2 et12.
  split.
  - apply sim_1; apply er12; auto.
  - intros.
    edestruct sim_1 as [_ [X2 [e2 [k2 [? []]]]]]; eauto.
    apply er12; eauto.
    exists X2, e2, k2.
    split; [| split]; auto.
    intros; apply er12; auto.
Qed.

Definition flip {A B C} (r : A -> B -> C) : B -> A -> C :=
  fun b a => r a b.

Definition is_bisimulation r : Prop :=
  is_simulation r /\ is_simulation (flip r).

Definition bisimilar (t1 t2 : itree E R) : Prop :=
  exists r : relation (itree E R),
    is_bisimulation r /\ r t1 t2.

Lemma flip_is_simulation :
  forall r,
    Symmetric r -> is_simulation r -> is_simulation (flip r).
Proof.
  unfold flip.
  intros r Symmetric_r r_is_simulation t1 t2 e; split.
  - now apply r_is_simulation.
  - intros X1 e1 k1 Hsteps1.
    destruct (r_is_simulation t1 t2) as [_ Hvis]; auto.
    destruct (Hvis X1 e1 k1 Hsteps1) as [X2 [e2 [k2 H]]].
    exists X2, e2, k2.
    firstorder.
Qed.

Lemma eq_is_simulation :
  is_simulation eq.
Proof.
  intros t1 t2 []; split.
  - auto.
  - intros X1 e1 k1 [t1' [Huntau1 Hobs1]].
    exists X1, e1, k1. split; [| split].
    + now exists t1'.
    + reflexivity.
    + intros; now apply JMeq_congr.
Qed.

Lemma eq_is_bisimulation : is_bisimulation eq.
Proof.
  split.
  - apply eq_is_simulation.
  - apply flip_is_simulation; auto.
    apply eq_is_simulation.
Qed.

Global Instance Reflexive_bisimilar : Reflexive bisimilar.
Proof.
  exists eq; auto using eq_is_bisimulation.
Qed.

Lemma flip_is_bisimulation :
  forall r, is_bisimulation r -> is_bisimulation (flip r).
Proof. firstorder. Qed.

Global Instance Symmetric_bisimilar : Symmetric bisimilar.
Proof.
  intros t1 t2 [r Hr].
  exists (flip r).
  firstorder.
Qed.

Definition compo {A B C} (rAB : A -> B -> Prop)
           (rBC : B -> C -> Prop) : A -> C -> Prop :=
  fun a c => exists b, rAB a b /\ rBC b c.

Lemma compo_is_simulation :
  forall r12 r23,
    is_simulation r12 -> is_simulation r23 ->
    is_simulation (compo r12 r23).
Proof.
  intros r12 r23 sim_12 sim_23 t1 t3 [t2 [H12 H23]].
  split.
  - intros. eapply sim_23; eauto. eapply sim_12; eauto.
  - intros X1 e1 k1 Hsteps1.
    edestruct (sim_12 t1 t2) as [_ [X2 [e2 [k2 [? []]]]]]; eauto.
    edestruct (sim_23 t2 t3) as [_ [X3 [e3 [k3 [? []]]]]]; eauto.
    exists X3, e3, k3.
    split; [| split].
    + auto.
    + eapply eq_dep_trans; eauto.
    + intros x1 x3 ex13.
      assert (I2 : exists x2 : X2, JMeq x1 x2 /\ JMeq x2 x3).
      { inversion_clear H0. exists x1; auto. }
      firstorder.
Qed.

Lemma flip_compo {A B C} (rAB : A -> B -> Prop)
      (rBC : B -> C -> Prop) :
  equiv (flip (compo rAB rBC))
        (compo (flip rBC) (flip rAB)).
Proof.
  firstorder.
Qed.

Lemma compo_is_bisimulation :
  forall r12 r23,
    is_bisimulation r12 -> is_bisimulation r23 ->
    is_bisimulation (compo r12 r23).
Proof.
  intros ? ? [] []; split.
  - auto using compo_is_simulation.
  - eapply is_simulation_equiv.
    + symmetry; apply flip_compo.
    + auto using compo_is_simulation.
Qed.

Global Instance Transitive_bisimilar : Transitive bisimilar.
Proof.
  intros t1 t2 t3 [r12 Hr12] [r23 H23].
  exists (compo r12 r23).
  split.
  - apply compo_is_bisimulation; firstorder.
  - firstorder.
Qed.

Theorem bisimilar_is_simulation : is_simulation bisimilar.
Proof.
  intros t1 t2 [r [[Hsim ?] et]]; split.
  - apply Hsim; auto.
  - intros X1 e1 k1 Hsteps1.
    edestruct Hsim as [_ [X2 [e2 [k2 [? []]]]]]; eauto.
    exists X2, e2, k2; repeat split; auto.
    exists r; firstorder.
Qed.

Theorem bisimilar_is_bisimulation : is_bisimulation bisimilar.
Proof.
  split.
  - apply bisimilar_is_simulation.
  - apply flip_is_simulation.
    + apply Symmetric_bisimilar.
    + apply bisimilar_is_simulation.
Qed.

End Bisimilarity.

Definition bind_sim {E A B}
           (t1 t2 : itree E A)
           (k1 k2 : A -> itree E B) : itree E B -> itree E B -> Prop :=
  fun m1 m2 =>
    bisimilar m1 m2 \/
    exists t1' t2' : itree E A,
      m1 = bind t1' k1 /\
      m2 = bind t2' k2 /\
      bisimilar t1' t2'.

Theorem bind_sim_is_simulation {E A B}
        (t1 t2 : itree E A) (k1 k2 : A -> itree E B)
        (Ht : bisimilar t1 t2)
        (Hk : forall a, bisimilar (k1 a) (k2 a)) :
  is_simulation (bind_sim t1 t2 k1 k2).
Proof.
  intros t10 t20 [ [? [[] ]] | [t1' [t2' [? [? [r' [[] ]]]]]]].
  - split.
    + apply H; auto.
    + intros. edestruct H as [_ [X2 [e2 [k2' [? []]]]]]; eauto.
      exists X2, e2, k2'. repeat split; auto.
      intros.
      left.
      exists x. firstorder.
  - split.
    + intros.
      assert (exists a0, steps t1' (RetF a0) /\ steps (k1 a0) (RetF a)).
      { admit. }
      destruct H5 as [a0 []].
      apply H1 in H3.
      apply H3 in H5.
      destruct (Hk a0) as [? [[]]].
      apply H7 in H9.
      apply H9 in H6.
      admit.
    + intros X1 e1 k1' Hsteps1.
      assert (exists a0, steps t1' (RetF a0) /\ steps (k1 a0) (VisF e1 k1')).
      { admit. }
      destruct H4 as [a0 []].
      apply H1 in H3.
      apply H3 in H4.
      destruct (Hk a0) as [? [[]]]; eauto.
      edestruct H6 as [? [X2 [e2 [k2' [? []]]]]]; eauto.
      exists X2, e2, k2'; split; [| split]; auto. { admit. }
      firstorder.
Admitted.

Definition flip_bind_sim {E A B} (t1 t2 : itree E A)
           (k1 k2 : A -> itree E B) :
    equiv (bind_sim t1 t2 k1 k2)
          (flip (bind_sim t2 t1 k2 k1)).
Proof.
  intros ? ?; split; intros [].
  - left; symmetry; auto.
  - right; destruct H as [t1' [t2' [? []]]].
    exists t2', t1'. split; [|split]; auto. symmetry; auto.
  - left; symmetry; auto.
  - right; destruct H as [t2' [t1' [? []]]].
    exists t1', t2'; split; [|split]; auto. symmetry; auto.
Qed.

Theorem bind_bisimilar {E A B}
        (t1 t2 : itree E A) (k1 k2 : A -> itree E B)
        (Ht : bisimilar t1 t2)
        (Hk : forall a, bisimilar (k1 a) (k2 a)) :
  bisimilar (bind t1 k1) (bind t2 k2).
Proof.
  exists (bind_sim t1 t2 k1 k2).
  split.
  - split.
    + apply bind_sim_is_simulation; auto.
    + eapply is_simulation_equiv.
      apply flip_bind_sim.
      apply bind_sim_is_simulation; auto.
      symmetry; auto.
      intros; symmetry; auto.
  - right. exists t1, t2. auto.
Qed.
