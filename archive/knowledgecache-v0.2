Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Import ListNotations.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapInterface.

(* === Basic Types === *)
Definition client_id := nat.
Definition sample_id := nat.
Definition label := nat.
Definition hash := list nat.
Definition knowledge := list nat.
Definition sample := (client_id * sample_id)%type.

(* === Map Setup === *)
Module Sample_as_OT := PairOrderedType Nat_as_OT Nat_as_OT.
Module SampleMap := FMapAVL.Make(Sample_as_OT).
(*Module SampleFacts := FMapFacts.Facts(SampleMap).*)
Module SampleFacts := FMapFacts.WFacts_fun Sample_as_OT SampleMap.

(* === Cache State === *)
Record CacheState := {
  IH : SampleMap.t hash;
  IK : SampleMap.t knowledge;
  LI : label -> list sample;
  IR : SampleMap.t (list sample)
}.


Definition init_cache : CacheState :=
  {| IH := SampleMap.empty _;
     IK := SampleMap.empty _;
     LI := fun _ => [];
     IR := SampleMap.empty _ |}.

(* === Vector Utilities === *)
Fixpoint add_vectors (a b : list nat) : list nat :=
  match a, b with
  | x::xs, y::ys => (x + y)::(add_vectors xs ys)
  | _, _ => []
  end.

Fixpoint div_vector (v : list nat) (d : nat) : list nat :=
  match v with
  | x::xs => (x / d)::(div_vector xs d)
  | [] => []
  end.

Definition ensemble (vs : list knowledge) : knowledge :=
  match vs with
  | [] => []
  | h::t => div_vector (fold_left add_vectors t h) (length vs)
  end.

Definition hnsw_search (h : hash) (candidates : list (sample * hash)) : list sample :=
  map fst (firstn 2 candidates).

(* === Uploading Samples === *)
Definition upload_sample (cs : CacheState) (k i : nat) (lbl : label) (h : hash) : CacheState :=
  let s := (k, i) in
  let li' := s :: LI cs lbl in
  {| IH := SampleMap.add s h (IH cs);
     IK := SampleMap.add s (repeat 0 (length h)) (IK cs);
     LI := fun l => if Nat.eqb l lbl then li' else LI cs l;
     IR := IR cs |}.

(* === Building IR === *)
Fixpoint build_IR_for_label (samples : list sample)
                            (ih : SampleMap.t hash)
                            (acc : SampleMap.t (list sample)) : SampleMap.t (list sample) :=
  match samples with
  | [] => acc
  | s :: rest =>
      match SampleMap.find s ih with
      | None => build_IR_for_label rest ih acc
      | Some h =>
          let others := filter (fun x => if Sample_as_OT.eq_dec x s then false else true) samples in
          let pairs := map (fun x => (x, SampleMap.find x ih)) others in
          let valid := fold_right (fun p acc' =>
                          match p with (x, Some h') => (x, h') :: acc' | _ => acc' end) [] pairs in
          let neighbors := hnsw_search h valid in
          build_IR_for_label rest ih (SampleMap.add s neighbors acc)
      end
  end.

Definition build_IR (cs : CacheState) (lbl : label) : CacheState :=
  {| IH := IH cs;
     IK := IK cs;
     LI := LI cs;
     IR := build_IR_for_label (LI cs lbl) (IH cs) (IR cs) |}.

(* === Processing Samples === *)
Definition process_sample (cs : CacheState) (s : sample) (zk : knowledge) : CacheState :=
  match SampleMap.find s (IR cs) with
  | None => cs
  | Some _ =>
      {| IH := IH cs;
         IK := SampleMap.add s zk (IK cs);
         LI := LI cs;
         IR := IR cs |}
  end.

(* === Invariants === *)
Definition IH_in_LI cs :=
  forall s h, SampleMap.find s (IH cs) = Some h -> exists l, In s (LI cs l).

Definition IK_in_IH cs :=
  forall s k, SampleMap.find s (IK cs) = Some k -> exists h, SampleMap.find s (IH cs) = Some h.

Definition IR_neighbors_in_IK cs :=
  forall s ns, SampleMap.find s (IR cs) = Some ns ->
    Forall (fun n => exists z, SampleMap.find n (IK cs) = Some z) ns.

Definition LI_no_duplicates cs := forall l, NoDup (LI cs l).

Definition CacheInvariant cs :=
  IH_in_LI cs /\ IK_in_IH cs /\ IR_neighbors_in_IK cs /\ LI_no_duplicates cs.

(* === Async === *)
Record CacheStateAsync := {
  cache : CacheState;
  pending : list (sample * knowledge)
}.

Definition all_neighbors_ready (cs : CacheState) (s : sample) : bool :=
  match SampleMap.find s (IR cs) with
  | None => false
  | Some ns =>
      forallb (fun n =>
        match SampleMap.find n (IK cs) with
        | Some _ => true | None => false end) ns
  end.

Definition process_sample_async (cs : CacheStateAsync) (s : sample) (zk : knowledge) : CacheStateAsync :=
  if all_neighbors_ready cs.(cache) s then
    {| cache := process_sample cs.(cache) s zk; pending := cs.(pending) |}
  else
    {| cache := cs.(cache); pending := (s, zk) :: cs.(pending) |}.

Fixpoint flush_pending_list (c : CacheState) (pend : list (sample * knowledge)) : CacheStateAsync :=
  match pend with
  | [] => {| cache := c; pending := [] |}
  | (s, zk) :: rest =>
      if all_neighbors_ready c s then
        flush_pending_list (process_sample c s zk) rest
      else
        let cs' := flush_pending_list c rest in
        {| cache := cs'.(cache); pending := (s, zk) :: cs'.(pending) |}
  end.

Definition flush_pending (cs : CacheStateAsync) : CacheStateAsync :=
  flush_pending_list cs.(cache) cs.(pending).

Definition CacheInvariantAsync (cs : CacheStateAsync) := CacheInvariant cs.(cache).

(* === Invariant Lemmas === *)
Lemma upload_preserves_invariant :
  forall cs k i lbl h,
    CacheInvariant cs ->
    CacheInvariant (upload_sample cs k i lbl h).
Proof.
  intros cs k i lbl h [Hih [Hik [Hir Hnodup]]].
  repeat split; simpl.

  - (* IH_in_LI *)
    intros s hval Hfind.
    destruct (Sample_as_OT.eq_dec s (k, i)) as [Heq | Hneq].
    + (* Case: s = (k, i) *)
      assert (Heq_maps : IH (upload_sample cs k i lbl h) =
                         SampleMap.add (k, i) h (IH cs)) by reflexivity.
      rewrite Heq_maps in Hfind.

      pose proof (SampleFacts.add_eq_o
               (elt := hash)
               (IH cs)
               (k, i)
               s
               h
               Heq) as Hlookup_eq.

      rewrite Hlookup_eq in Hfind.
      inversion Hfind. subst hval.

      exists lbl. simpl. apply in_eq.


    + (* Case: s \u2260 (k, i) *)
      assert (
        Hlookup : SampleMap.find s (IH (upload_sample cs k i lbl h)) =
                  SampleMap.find s (IH cs)).
      {
        unfold upload_sample; simpl.
        apply SampleFacts.add_neq_o. congruence.
      }
      rewrite Hlookup in Hfind.
      destruct (Hih s hval Hfind) as [l Hl]. exists l.
      destruct (Nat.eqb l lbl) eqn:E.
      * simpl. apply in_cons. exact Hl.
      * simpl. exact Hl.

  - (* IK_in_IH *)
    intros s kval Hfind.
    destruct (Sample_as_OT.eq_dec s (k, i)) as [Heq | Hneq].
    + (* Case: s = (k, i) *)
      exists h.
      unfold upload_sample; simpl.
      apply SampleFacts.add_eq_o. exact Heq.
    + (* Case: s \u2260 (k, i) *)
      assert (
        Hlookup : SampleMap.find s (IH (upload_sample cs k i lbl h)) =
                  SampleMap.find s (IH cs)).
      {
        unfold upload_sample; simpl.
        apply SampleFacts.add_neq_o. congruence.
      }
      rewrite Hlookup in Hfind.
      destruct (Hik s kval Hfind) as [h' Hh']. exists h'. exact Hh'.

  - (* IR_neighbors_in_IK *)
    apply Hir.

  - (* LI_no_duplicates *)
    intros l.
    destruct (Nat.eq_dec l lbl) as [Heq | Hneq].
    + subst l.
      rewrite Nat.eqb_refl. simpl. constructor.
      * intro Hc. apply Hnodup in lbl. rewrite Nat.eqb_refl in lbl.
        inversion lbl. contradiction.
      * apply Hnodup.
    + rewrite Nat.eqb_neq in Hneq. rewrite if_false by assumption.
      apply Hnodup.
Qed.


Lemma build_IR_preserves_invariant :
  forall cs lbl,
    CacheInvariant cs ->
    CacheInvariant (build_IR cs lbl).
Proof.
  intros cs lbl Hinv.
  destruct Hinv as [Hih [Hik [Hir Hnodup]]].
  repeat split; simpl; eauto.
Qed.

Lemma process_sample_preserves_invariant :
  forall cs s zk,
    CacheInvariant cs ->
    SampleMap.In s (IR cs) ->
    (forall ns, SampleMap.find s (IR cs) = Some ns ->
                Forall (fun n => exists z, SampleMap.find n (IK cs) = Some z) ns) ->
    CacheInvariant (process_sample cs s zk).
Proof.
  intros cs s zk Hinv Hin Hready.
  destruct Hinv as [Hih [Hik [Hir Hnodup]]].
  repeat split; simpl.
  - (* IH_in_LI *)
    intros s' hval Hfind.
    destruct (Sample_as_OT.eq_dec s' s).
    + subst. apply Hih. assumption.
    + rewrite SampleMap.gso in Hfind by congruence. apply Hih in Hfind. exact Hfind.
  - (* IK_in_IH *)
    intros s' kval Hfind.
    destruct (Sample_as_OT.eq_dec s' s).
    + subst. exists (SampleMap.find s (IH cs)). destruct (SampleMap.find s (IH cs)); auto.
    + rewrite SampleMap.gso in Hfind by congruence. apply Hik in Hfind. exact Hfind.
  - (* IR_neighbors_in_IK *)
    intros s' ns Hf.
    destruct (Sample_as_OT.eq_dec s' s).
    + subst. rewrite SampleMap.gss in Hf. inversion Hf; subst. apply Hready. reflexivity.
    + rewrite SampleMap.gso in Hf by congruence. apply Hir. exact Hf.
  - exact Hnodup.
Qed.

Lemma flush_pending_preserves_invariant :
  forall base pend,
    CacheInvariant base ->
    (forall s zk, In (s, zk) pend ->
      SampleMap.In s (IR base) /\
      (forall ns, SampleMap.find s (IR base) = Some ns ->
                  Forall (fun n => exists z, SampleMap.find n (IK base) = Some z) ns)) ->
    CacheInvariant (flush_pending_list base pend).(cache).
Proof.
  intros base pend.
  revert base.
  induction pend as [|(s, zk) rest IH]; intros base Hinv Hconds.
  - simpl. exact Hinv.
  - simpl.
    destruct (SampleMap.find s (IR base)) eqn:Hs; [| apply IH; auto].
    destruct (forallb (fun n =>
                match SampleMap.find n (IK base) with
                | Some _ => true | None => false end) l) eqn:Hb.
    + (* neighbors ready: flush it *)
      assert (Hin : SampleMap.In s (IR base)) by (apply SampleMap.find_2; exact Hs).
      assert (Hok : forall ns, SampleMap.find s (IR base) = Some ns ->
                  Forall (fun n => exists z, SampleMap.find n (IK base) = Some z) ns).
      { intros. apply Hconds with (zk := zk). simpl. auto. }
      apply IH. apply process_sample_preserves_invariant; auto.
      intros x z Hin'. apply Hconds; simpl. right. exact Hin'.
    + (* skip this one, try rest *)
      apply IH; auto. intros x z Hin'. apply Hconds; simpl. right. exact Hin'.
Qed.