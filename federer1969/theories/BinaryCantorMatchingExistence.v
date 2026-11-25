(** Federer (1969), 3.4.4, p. 318: prove
    existence of the correspondence between the original Cantor sets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  CompactNestedIntersection BinaryCantorCodingUP BinaryCantorCodingLaws
  BinaryCantorAddressUniqueness BinaryCantorMatchingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_cantor_correspondence_exists]:
    the induced phi in 3.4.4, p. 318. Unique
    original addresses at each source level form a consistent
    path. The corresponding original target intervals are nested,
    nonempty, and compact. Their actual intersection supplies a
    target point respecting every address. The selected function
    remains local; no correspondence or limit point is assumed. *)
Theorem binary_original_cantor_correspondence_exists (R:realType) (rho sigma:R)
    JA HA I a JB HB J b (A B:set (real_line_metric R)):
  is_binary_original_coding rho JA HA I a ->
  is_binary_original_coding sigma JB HB J b ->
  is_special_interval_tree_limit HA A ->is_special_interval_tree_limit HB B ->
  0<rho ->0<1-2*rho ->0<=sigma ->sigma<=1 ->
  exists phi:R->R,is_binary_cantor_correspondence A B I J phi.
Proof.
move=>hI hJ hA hB hRho hGap hSigma hSigmaUpper.
have hPoint (x:real_line_metric R) (hx:A x):exists y:real_line_metric R,
    B y /\forall v,val (I v) x ->val (J v) y.
  have hEach j:exists w,size w=j /\val (I w) x.
    exact:(@binary_original_point_address_exists R rho JA HA I a A hI hA x hx j).
  have [w hw]:=choice hEach.
  have hStep j:exists c,w j.+1=rcons (w j) c.
    exact:(@binary_original_point_address_step R rho JA HA I a hI hRho hGap
      j (w j) (w j.+1) x (hw j).1 (hw j.+1).1 (hw j).2 (hw j.+1).2).
  pose C j:set (real_line_metric R):=val (J (w j)).
  have hTail i l:C (i+l)%N `<=` C i.
    elim:l=>[|l ih];first by rewrite addn0.
    rewrite addnS.
    have [c hC]:=hStep (i+l)%N.
    move=>y hy;apply:ih.
    have hyChild:val (J (rcons (w (i+l)%N) c)) y by move:hy;rewrite /C hC.
    exact:(@binary_original_coding_child_subset R sigma JB HB J b hJ hSigma hSigmaUpper
      (w (i+l)%N) c y hyChild).
  have hDecreasing i j (hij:(i<=j)%N):C j `<=` C i.
    have h:=hTail i (j-i)%N.
    have hIndex:(i+(j-i))%N=j by rewrite subnKC.
    by rewrite hIndex in h.
  have hCompact:compact (C 0%N):=compact_real_interval_compact (set_valP (J (w 0%N))).
  have hClosed j:closed (C j):=compact_real_interval_closed (set_valP (J (w j))).
  have hNonempty j:C j !=set0:=compact_real_interval_nonempty (set_valP (J (w j))).
  have [y hy]:=compact_nested_nonempty_intersection hCompact hClosed hDecreasing hNonempty.
  exists y;split.
  - apply:(hB y).2=>j.
    exists (J (w j));split.
    + apply/(binary_original_coding_levels hJ j (J (w j))).
      exists (w j);by split;first exact:(hw j).1.
    + exact:hy j Logic.I.
  - move=>v hv.
    have hSame:v=w (size v):=@binary_original_address_point_unique R rho JA HA I a hI hRho hGap
      (size v) v (w (size v)) x erefl (hw (size v)).1 hv (hw (size v)).2.
    rewrite hSame;exact:hy (size v) Logic.I.
have hEach (x:real_line_metric R):exists y:real_line_metric R,
    A x ->B y /\forall v,val (I v) x ->val (J v) y.
  case:(pselect (A x))=>hx.
  - have [y hy]:=hPoint x hx;exists y;by move=>_.
  - exists 0=>hFalse;exact:False_ind _ (hx hFalse).
have [phi hPhi]:=choice hEach.
exists phi;constructor.
- move=>x hx;exact:(hPhi x hx).1.
- move=>v x hx hv;exact:(hPhi x hx).2 v hv.
Qed.
