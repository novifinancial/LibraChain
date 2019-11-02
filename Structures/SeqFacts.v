From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.

Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***************************************************)
(*        Some useful facts about lists            *)
(***************************************************)

Section SeqFacts.

Variable T: eqType.

Implicit Types (x y :T).

Lemma rem_neq x y ls :
  x != y -> x \in ls -> x \in seq.rem y ls.
Proof.
move=>N; elim: ls=>//h ls Hi.
rewrite inE; case/orP=>//=.
- by move/eqP=>Z; subst h; move/negbTE: N=>->; rewrite inE eqxx.
by case: ifP=>//=N' /Hi; rewrite inE orbC=>->.
Qed.

Lemma rem_neq_notin x y ls:
  x != y -> x \notin ls -> x \notin seq.rem y ls.
Proof.
move=>N; elim: ls=>//h ls Hi.
rewrite inE; case/norP=>//=.
move=>Neq Ni; specialize (Hi Ni); case: ifP=>//=.
by move=>Hy; rewrite inE; apply/norP; rewrite Hi.
Qed.

Lemma in_seq x xs:
  x \in xs -> exists fs ls, xs = fs ++ x :: ls.
Proof.
move=>H. elim: xs H; first done.
move=>h t Hi; rewrite in_cons; move/orP; case.
by move/eqP=>->; exists [::], t.
by move=>H; move: (Hi H); move=>[fs] [ls]=>->; exists (h :: fs), ls.
Qed.

Lemma in_seq_neq x xs :
  x \in xs -> exists fs ls, xs = fs ++ x :: ls /\ x \notin fs.
Proof.
move=>H. elim: xs H; first done.
move=>h t Hi; rewrite in_cons; move/orP; case.
by move/eqP=>->; exists [::], t.
move=>H; move: (Hi H); move=>[fs][ls][->]G.
case E: (x == h); last first.
- by exists (h :: fs), ls; split; rewrite ?cat_cons// inE E G.
by exists [::], (fs ++ x :: ls); split; move/eqP:E=>->.
Qed.

Lemma in_seq_excl x y (xs: seq T):
  x \in xs -> y \notin xs -> x != y.
Proof.
elim: xs=>[|h tl Hi]//.
rewrite !in_cons; case/orP=> H; case/norP=>H0.
by move/eqP in H; subst h=>_; rewrite eq_sym.
by move=> H'; apply (Hi H H').
Qed.

Lemma nth_in_default_irrel x0 y0 s (i: nat):
  i < size s ->
  nth x0 s i = nth y0 s i.
Proof.
elim: i s => [|n IHn] s; case: s => [| q qs] /=; first by rewrite ltn0.
- by [].
- by rewrite ltn0.
- by rewrite ltnS => HH; rewrite IHn.
Qed.

Lemma not_in_filter_predC1 x s :
  x \notin filter (predC1 x) s.
Proof.
elim: s=> [|y ys IHs] //=; case H: (y == x)=> /=; first by apply IHs.
by rewrite in_cons eq_sym H orFb IHs.
Qed.

Lemma not_in_all_predC1 x s:
  all (predC1 x) s = (x \notin s).
Proof.
elim: s => [|y s IHs] //.
rewrite in_cons /all -/(all (predC1 x)) {1}/predC1 negb_or eq_sym /=.
by apply: andb_id2l.
Qed.

Fixpoint rundup (s: seq T) :=
  if s is x :: s' then x :: (filter (predC1 x) (rundup s')) else [::].

Lemma size_rundup s : size (rundup s) <= size s.
Proof. elim: s => //= x s IHs; rewrite size_filter.
by apply: (leq_ltn_trans (count_size _ _)).
Qed.

Lemma mem_rundup s : rundup s =i s.
Proof.
move=> x; elim: s => //= y s IHs; rewrite 2!inE -IHs.
by case H:(x == y) => //=; rewrite mem_filter /= H.
Qed.

Lemma rundup_uniq s : uniq (rundup s).
Proof.
elim: s => //= x s IHs; rewrite mem_filter /= eq_refl /=.
by rewrite filter_uniq.
Qed.

Lemma rundup_id s : uniq s -> rundup s = s.
Proof.
elim: s => //= x s IHs /andP [H /IHs->].
have/all_filterP: (all (predC1 x) s)=>[|->] //.
rewrite all_predC; apply/hasP=> [[x1 Hx1]]; move/eqP=> eqxx1.
by move: H; rewrite -eqxx1; move/negP.
Qed.

Lemma predC_pred1 x : pred1 x =1 [eta predC [pred x0 | x0 != x]].
Proof.
move=> x0; apply/eqP.
rewrite /predC /=; case H: (x0 == x)=> /=; by apply/eqP; rewrite ?H.
Qed.

Lemma count_predC1Pn x s : (count (predC1 x) s == size s) = (x \notin s).
Proof.
rewrite /predC1 -(count_predC [pred x0| x0 != x]) -{1}[count _ s]addn0 -has_pred1 has_filter.
rewrite eqn_add2l -size_filter eq_sym; apply/nilP; rewrite if_neg -(eq_filter (predC_pred1 x)).
case H: ([seq x0 <- s| (pred1 x) x0] == [::])=> /=; apply/eqP; first by [].
by rewrite H.
Qed.

Lemma all_filter (a: pred T) (s: seq T): (filter a s == s) = all a s.
Proof.
by apply/eqP; case H: (all a s); apply/all_filterP; [|rewrite H].
Qed.

Lemma all_notin (s: seq T) x: (all (predC1 x) s) = (x \notin s).
Proof.
elim: s =>[| x0 s IHs] //; rewrite in_cons /= negb_or IHs.
by apply andb_id2r; rewrite eq_sym.
Qed.

Lemma ltn_size_rundup s : (size (rundup s) < size s) = ~~ uniq s.
Proof.
case Huniq: (uniq s) =>/=; first by move/rundup_id: Huniq=>->; rewrite ltnn.
apply: idP; move/negP: Huniq; elim: s => [| x s IHs] //=; rewrite ltnS.
move/negP; rewrite negb_and; move/orP=> [Hnin|Hnuniq].
- move: Hnin; rewrite -mem_rundup -count_predC1Pn=> Hnin.
  move: (count_size (predC1 x) (rundup s)); rewrite leq_eqVlt; move/negbTE: Hnin=>->.
  rewrite orFb size_filter; move/leq_trans; apply; exact: size_rundup.
rewrite size_filter; apply: (leq_ltn_trans (count_size (predC1 x) (rundup s))).
by rewrite IHs //; apply/negP.
Qed.

Lemma rundup_nil s : rundup s = [::] -> s = [::].
Proof. by case: s => //= x s; rewrite -mem_rundup; case: ifP; case: rundup. Qed.

Lemma predIC (p q: pred T) : predI p q =1 predI q p.
Proof.
by move => x /=; rewrite andbC.
Qed.

Lemma filter_rundup p s : filter p (rundup s) = rundup (filter p s).
Proof.
elim: s => //= x s IHs; rewrite (fun_if rundup) /= fun_if -filter_predI.
rewrite (eq_filter (predIC p _)) filter_predI IHs; case H: (p x) => //=.
apply/eqP; rewrite all_filter all_notin.
by rewrite -IHs mem_filter H andFb.
Qed.

Lemma predC1_eq s x: x::s =i x::(filter (predC1 x) s).
Proof.
move=> y; rewrite 2!in_cons; case Hyx: (y == x); first by [].
by rewrite 2!orFb mem_filter /= Hyx andTb.
Qed.

Lemma predC1_split s x: x \in s -> s =i x::(filter (predC1 x) s).
Proof.
elim: s=> [|y s IHs] Hx //.
move: Hx; rewrite in_cons; case Hxy: (x == y).
- by move/eqP: Hxy=>-> _; rewrite /filter {1}/predC1 /= eq_refl; apply: predC1_eq.
rewrite orFb; move/IHs=> Hs; rewrite /filter {1}/predC1 /= eq_sym Hxy /=.
move=> z; rewrite 3!in_cons; case Hx: (z == y); first by rewrite orbT.
rewrite 2!orFb -in_cons; move: z {Hx}; apply Hs.
Qed.

Lemma rem_elem (p : T) xs ys :
  p \notin xs-> seq.rem p (xs ++ p :: ys) = xs ++ ys.
Proof.
elim: xs=>//=; first by rewrite eqxx.
move=>x xs Hi; rewrite inE=>/norP[H1 H2].
by move/negbTE: H1; rewrite eq_sym=>->; rewrite (Hi H2).
Qed.

Lemma dom_ord1 {K: ordType} (j : K) (w : T) m :
  valid (j \\-> w \+ m) ->
  path ord j (dom m) ->
  dom (j \\-> w \+ m) = j :: (dom m).
Proof.
elim/um_indf: m=>/=[||k v m Hi V' P' V P].
- by case: validUn=>//=_; rewrite valid_undef.
- by rewrite unitR dom0 domPtK.
rewrite -joinCA in V; move: (Hi (validR V))=>{Hi}Hi.
have A: antisymmetric ord by move=>???/andP[]H1 H2; move: (nsym H1 H2).
apply: (eq_sorted (@trans K) (A K))=>//=.
rewrite joinCA in V.
apply: uniq_perm=>/=; rewrite ?dom_uniq ?[_&&true]andbC//=.
- case: validUn V=>//_ _/(_ j).
  by rewrite domPtK inE eqxx uniq_dom=>/(_ is_true_true) ? ?; apply/andP.
move=>z; rewrite !inE !domUn !inE V domPtK inE (eq_sym z k).
by rewrite (validR V)/= domPtUn V'/= domPtK !inE.
Qed.

Lemma path_ord_sorted {K: ordType} z j (l : seq K) :
  sorted ord l -> path ord j l -> z \in l -> ord j z.
Proof.
elim: l z=>//h l Hi z/=P/andP[O _].
rewrite inE; case/orP; first by move/eqP=>->.
move=>I; apply: Hi=>//; first by apply:(path_sorted P).
clear I z; case: l O P=>//=x xs O/andP[O' ->]; rewrite andbC/=.
by apply: (@trans K _ _ _ O O').
Qed.

Lemma dom_ord2 {K: ordType} (j k : K) (w v : T) m:
  valid (k \\-> v \+ (j \\-> w \+ m)) ->
  path ord j (dom m) ->
  dom (pts j w \+ (k \\-> v \+ m)) =
  if ord j k then j :: dom (k \\-> v \+ m) else k :: j :: (dom m).
Proof.
have A: antisymmetric ord by move=>???/andP[]H1 H2; move: (nsym H1 H2).
case: ifP=>X V P; rewrite joinCA in V.
- apply: (eq_sorted (@trans K) (A K))=>//=.
  + rewrite path_min_sorted//.
    move=>z; rewrite domUn inE (validR V) domPtK inE /=.
    case/orP; first by move/eqP=>->.
    by move/(path_ord_sorted (sorted_dom m) P).
  apply: uniq_perm=>/=; rewrite ?dom_uniq ?[_&&true]andbC//=.
  + by case: validUn V=>//_ _/(_ j);
       rewrite domPtK inE eqxx=>/(_ is_true_true) ? ?; apply/andP.
  move=>z; rewrite !inE !domUn !inE V domPtK inE /=.
  by rewrite (validR V)/= domPtUn /= domPtK !inE (validR V) (eq_sym z k).
apply: (eq_sorted (@trans K) (A K))=>//=.
- rewrite P andbC/=; case/orP: (total k j) X=>///orP[]; last by move=>->.
  move/eqP=>Z; subst j.
  case: validUn (V)=>//_ _/(_ k); rewrite domPtK inE eqxx=>/(_ is_true_true).
  by rewrite domUn inE domPtK inE eqxx/= andbC(validR V).
apply: uniq_perm=>/=; rewrite ?dom_uniq ?[_&&true]andbC//=.
- rewrite joinCA in V; case: validUn (V)=>//_ _/(_ k).
  rewrite domPtK inE eqxx=>/(_ is_true_true)=>/negP N _.
  apply/andP; split; last first.
  + case: validUn (validR V)=>//_ _/(_ j).
    by rewrite domPtK inE eqxx=>/(_ is_true_true) ? ?; apply/andP.
  rewrite inE; apply/negP=>M; apply: N.
  by rewrite domUn inE (validR V) domPtK inE.
move=>z; rewrite !inE !domUn !inE V domPtK inE eq_sym/=.
rewrite domUn inE (validR V)/= domPtK inE.
by case: (j == z)=>//; case: (z == k).
Qed.

Lemma dom_insert {K: ordType} (k : K) (v : T) m :
  valid (k \\-> v \+ m) ->
  exists ks1 ks2, dom m = ks1 ++ ks2 /\
                  dom (k \\-> v \+ m) = ks1 ++ k :: ks2.
Proof.
move=>V; elim/um_indf: m V=>//[||j w m' Hi V' P V].
- by case: validUn=>//=_; rewrite valid_undef.
- by rewrite unitR dom0 domPtK; exists [::], [::].
move: (V); rewrite -joinCA=>/validR/Hi[ks1][ks2][E1]E2.
(* So, j < (dom m'), hence it goes at the head *)
rewrite (dom_ord1 V' P) E1 (dom_ord2 V P) !E1 E2.
case: ifP=>_; first by exists (j :: ks1), ks2.
by exists [::], (j :: ks1 ++ ks2).
Qed.

End SeqFacts.
