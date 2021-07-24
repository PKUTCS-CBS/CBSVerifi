(**

This file describes the representation and properties of CBS-heap predicates.

Author: Bowen Zhang.

Date : 2021.07.24
*)

Set Implicit Arguments.
From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* CBS *) Require Export Language InnerPre.

(*** ============  CBS-heap predicates ====================== ***)
Definition hprop := heap -> Prop.

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

Open Scope hprop_scope.

Definition qimpl {A} (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Types Hb : hbprop.
Implicit Types Hf : hfprop.
Implicit Types Qb : val->hbprop.
Implicit Types Qf : val->hfprop.


Definition getheapf (h:heap): heapf :=
  match h with (hf,hb) => hf end.
Definition getheapb (h:heap): heapb :=
  match h with (hf,hb) => hb end.

Notation "h '`f' " := (getheapf h)
  (at level 20) : heap_scope.
Notation "h '`b' " := (getheapb h)
  (at level 20) : heap_scope.

Open Scope heap_scope.

Lemma state_get_eq : forall h, h = (h `f, h `b).
Proof. 
  destruct h. simpl. reflexivity. Qed.

Definition glounion h1 h2 := 
  (h1`f \+ h2`f, h1`b \+ h2`b).

Definition glodisjoint h1 h2 := 
  Fmap.disjoint (h1`f) (h2`f) /\ Fmap.disjoint (h1`b) (h2`b).

Notation "h1 \g h2" := (glounion h1 h2)
  (at level 37, right associativity).

Notation "h1 _|_ h2" := ( glodisjoint h1 h2)
  (at level 37, right associativity).

(* ================================================================= *)
(** Core CBS heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal **)

Definition RefineAssn (Hf:hfprop) (Hb:hbprop): hprop := 
  fun h => Hf (h`f) /\ Hb (h`b).

Notation "'\R[' Hf ',' Hb ']'" := (RefineAssn Hf Hb) (at level 50) : hprop_scope.

(* empty *)

Definition hempty : hprop :=
  fun h => (h`f) = Fmap.empty /\ (h`b) = Fmap.empty.

Definition hexists {A:Type} (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Definition hforall_Assn (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Definition hstar (H1 H2:hprop): hprop := 
  fun h => exists h1 h2, 
    H1 h1 
  /\ H2 h2
  /\ h1 _|_ h2
  /\ h = h1 \g h2.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'") : hprop_scope.

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.


(** ------------ CBS Assn himpl --------  **)
Lemma himpl_inv : forall H1 H2 h,
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. unfolds*. intros. apply himpl_refl. Qed.

Hint Resolve himpl_refl qimpl_refl state_get_eq.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] (hf_empty,hb_empty).
Proof using. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = (hf_empty,hb_empty).
Proof using.
  introv M.
  destruct M as (M1&M2).
  rewrite <- M1,<- M2.
  auto.
 Qed.

Lemma hempty_refine : 
  \[] = \R[\f[],\b[]].
Proof. unfolds*. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hstar_sep_l : forall Hf Hb Hf' Hb',
  (\R[ Hf, Hb ]) \* (\R[ Hf', Hb'])
==>
  \R[(Hf \f* Hf'), (Hb \b* Hb')].
Proof.
  introv.
  introv M.
  destruct M as (h1&h2&HA&HB&(HC1&HC2)&HD).
  destruct HA as (HA1&HA2).
  destruct HB as (HB1&HB2).
  subst. splits; simpl.
  applys~ hfstar_intro.
  applys~ hbstar_intro.
Qed.

Lemma hstar_sep_r : forall Hf Hb Hf' Hb',
  \R[(Hf \f* Hf'), (Hb \b* Hb')]
==>
  (\R[ Hf, Hb ]) \* (\R[ Hf', Hb' ]).
Proof.
  introv.
  introv M.
  destruct M as (HA&HB).
  destruct HA as (sf1&sf2&HB1&HB2&HB3&HB4).
  destruct HB as (sb1&sb2&HC1&HC2&HC3&HC4).
  exists (sf1,sb1) (sf2,sb2). splits.
  splits~. splits~. splits~.
  unfold glounion. simpl.
  rewrite <- HB4, <- HC4.
  auto.
Qed.

Lemma hstar_sep: forall Hf Hb Hf' Hb',
  (\R[ Hf, Hb ]) \* (\R[ Hf', Hb' ])
=
  \R[(Hf \f* Hf'), (Hb \b* Hb')].
Proof.
  intros. apply himpl_antisym.
  apply hstar_sep_l.
  apply hstar_sep_r.
Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 -> H2 h2 ->
  Fmap.disjoint (h1`f) (h2`f) 
  /\ Fmap.disjoint (h1`b) (h2`b) 
  -> (H1 \* H2) (h1 \g h2).
Proof. intros. exists h1 h2. splits~. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ h1 _|_ h2 /\ h = h1 \g h2.
Proof.
  introv M1.
  destruct M1 as (h1&h2&MA&MB&MC&MD).
  exists~ h1 h2.
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. unfold hprop, hstar. intros H1 H2.
  intros h (h1&h2&HA&HB&(HC&HD)&HE).
  exists h2 h1.
  splits~. splits~.
  unfold glounion.
  rewrite~ Fmap.union_comm_of_disjoint.
  remember (h1 `f \+ h2 `f) as A.
  rewrite~ Fmap.union_comm_of_disjoint.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  - intros (h12&h3&M).
    destruct M as (M1&M2&(M3&M4)&M6).
    rewrite M6.
    destruct M1 as (h1&h2&MA&MB&(MC&MD)&MF).
    unfolds glounion.
    subst. simpls. exists h1 (h2 \g h3).
    splits~. applys~ hstar_intro.
    rewrite disjoint_union_eq_l in M3, M4.
    splits; simpl;
    rewrite~ disjoint_union_eq_r.
  - introv M.
    destruct M as (h1&h23&M1&M2&(M3&M4)&M6).
    destruct M2 as (h2&h3&MA&MB&(MC&MD)&MF).
    unfolds glounion. subst. simpls.
    exists (h1 \g h2) h3. splits~. applys~ hstar_intro.
    rewrite disjoint_union_eq_r in M3, M4.
    splits; simpl; rewrite~ disjoint_union_eq_l.
    unfold glounion. simpl.
    do 2 rewrite union_assoc. auto.
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym; intros h M.
  destruct M as (h1&h2&HA&HB&(HC&HD)&HF).
  unfold glounion in HF.
  apply hempty_inv in HA.
  subst. simpls. 
  do 2 rewrite union_empty_l.
  rewrite~ <- state_get_eq.
  
  exists (hf_empty,hb_empty) h.
  splits~. applys hempty_intro.
  splits; simpl; apply disjoint_empty_l. 
  unfold glounion. simpl.
  do 2 rewrite union_empty_l. auto.
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  intros.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm.
  applys hstar_hempty_l.
Qed.

Lemma hstar_hempty_l' : forall H,
  \R[\f[],\b[]] \* H = H.
Proof using.
  rewrite <- hempty_refine.
  intros. apply hstar_hempty_l.
Qed.

Lemma hstar_hempty_r' : forall H,
  (H \* \R[\f[],\b[]]) = H.
Proof using.
  intros.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm.
  applys hstar_hempty_l.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using.
  introv W. intros h M.
  destruct M as (h1&h2&MA&MB&MC).
  exists~ h1 h2.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M.
  do 2 rewrite (@hstar_comm H1).
  applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1.
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hstar_hpure : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hstar_hpure. Qed.


(*========== some additional lemmas (useful in parctice) ==========*)

Lemma hbstar_comm3 : forall (H1 H2 H3 : hbprop),
   H1 \b* H2 \b* H3 = H3 \b* H2 \b* H1.
Proof.
  intros. rewrite <- hbstar_assoc, hbstar_comm.
  remember (H1 \b* H2) as E eqn:M.
  rewrite hbstar_comm in M. rewrite~ M.
Qed.

Lemma listtoapp3 : forall (p1 p2 p3: bloc),
  (p1 :: p2 :: p3 :: nil) = (p1 :: p2 :: nil) ++ (p3 :: nil).
Proof. intros. rew_list~. Qed.

Lemma himpl_hbexists : forall Hf Hb l,
(fun x : val =>
 (\R[ \f[], \existsb bp0 : bloc, \b[x = val_bloc bp0] \b* bp0 ~b~> l]) \*
 (\R[ Hf, Hb])) ===>
(fun r : val =>
 \R[ Hf,
 \existsb bp' : bloc, \b[r = val_bloc bp'] \b* bp' ~b~> l \b* Hb]).
Proof.
  intros. intros r.
  rewrite hstar_sep.
  intros h (MA&MB). splits~.
  rewrite hfstar_hempty_l in MA. auto.
  rewrite hbstar_hexists in MB.
  destruct MB as (bp'&MB). rewrite hbstar_assoc in MB.
  exists~ bp'.
Qed.

Lemma himpl_noduplicate2 : forall bp1 bp2 l1 l2,
\R[ \f[], bp1 ~b~> l1 \b* bp2 ~b~> l2] ==>
\R[ \f[noduplicates (bp1 :: bp2 :: nil)], bp1 ~b~> l1 \b* bp2 ~b~> l2].
Proof.
  intros. intros h (MA&MB). splits~.
  apply hf_empty_inv in MA. rewrite MA.
  apply hfpure_intro, noduplicates_two.
  intro N. rewrite N in MB.
  applys hbstar_hsingle_same_loc MB.
Qed.

Lemma hbstar_noduplicates3 : forall h p1 p2 p3 l1 l2 l3,
  (p1 ~b~> l1 \b* p2 ~b~> l2 \b* p3 ~b~> l3) (h `b) ->
  noduplicates (p1 :: p2 :: p3 :: nil).
Proof.
  introv M. rewrite listtoapp3.
  applys noduplicates_app.
  - applys noduplicates_two.
    lets N1 : hbstar_hsingle_same_loc p1.
    rewrite <- hbstar_assoc in M.
    destruct M as (hb1&hb2&M1&M).
    intro N. rewrite <- N in M1.
    apply N1 in M1. apply M1.
  - applys noduplicates_one.
  - intros p N1 N2.
    rewrite mem_cons_eq in N1.
    destruct N1.
    rewrite mem_one_eq in N2.
    subst. rewrite hbstar_comm in M.
    rewrite hbstar_assoc in M.
    destruct M as (hb1&hb2&M1&M2&M3).
    lets N1 : hbstar_hsingle_same_loc p3.
    apply N1 in M2. apply M2.
    rewrite mem_cons_eq in N2. destruct~ N2.
    rewrite mem_cons_eq in H. destruct~ H.
    subst. destruct M as (hb1&hb2&M1&M2&M3).
    lets N1 : hbstar_hsingle_same_loc p3.
    apply N1 in M2. apply M2.
    rewrite~ mem_nil_eq in H.
    rewrite~ mem_nil_eq in H0.
Qed.

Lemma himpl_noduplicate3 : forall bp1 bp2 bp3 l1 l2 l3,
\R[ \f[], bp1 ~b~> l1 \b* bp2 ~b~> l2 \b* bp3 ~b~> l3] ==>
\R[ \f[noduplicates (rev (bp3 :: bp2 :: bp1 :: nil))], 
    bp1 ~b~> l1 \b* bp2 ~b~> l2 \b* bp3 ~b~> l3].
Proof.
  intros. intros h (MA&MB). splits~.
  apply hf_empty_inv in MA. rewrite MA.
  applys hfpure_intro. applys hbstar_noduplicates3 MB.
Qed.