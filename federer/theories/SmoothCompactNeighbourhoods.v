(** Federer (1969), 4.1.14, p. 370: the compact
    image f(K) has compact neighbourhoods inside V, and
    a limit supported in every such neighbourhood is
    supported in f(K). Reuse the preceding opaque compact
    exhaustion of 4.1.1, p. 344. The proof chooses
    no point from the compact set and includes empty sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis
  SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactExhaustionSealed
  IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section SmoothCompactNeighbourhoods.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Local Notation XT := (real_norm_metric_space hNX).

(** Source for [smooth_compact_neighbourhood_exists]: every
    original compact subset J of the open target V
    lies in the ambient interior of another compact
    subset of V, supporting the compact E in Federer
    4.1.14, p. 370. Empty J and V are allowed. *)
Theorem smooth_compact_neighbourhood_exists
    (V:set X) (hV:forall x,V x->norm_domain_interior NX V x)
    (J:smooth_compact_set hNX V):
  exists E:smooth_compact_set hNX V,forall x,
    smooth_compact_carrier J x->
    norm_domain_interior NX (smooth_compact_carrier E) x.
Proof.
pose A:=@SmoothCompactExhaustion.value R X NX hNX n b hb V hV.
pose hA:=@SmoothCompactExhaustion.laws R X NX hNX n b hb V hV.
have[j [W [hW [hJW hWA]]]]:=smooth_compact_exhaustion_neighbourhood hA J.
exists (A j)=>x hx.
have hInterior:norm_domain_interior NX W x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  rewrite openE in hW;exact:hW x (hJW x hx).
have[r [hr hInside]]:=hInterior.
exists r;split;first exact:hr.
move=>h hh;exact:hWA _ (hInside h hh).
Qed.

(** Source for [smooth_compact_neighbourhoods_detect_closed]:
    containment in every original compact neighbourhood of
    J forces containment in J, supporting the sharp
    image-support conclusion of Federer 4.1.14, p. 370.
    For a point outside J use the preceding exhaustion
    on V with that one point deleted. No nonempty
    compact-set premise or closure premise on B is used. *)
Theorem smooth_compact_neighbourhoods_detect_closed
    (V:set X) (hV:forall x,V x->norm_domain_interior NX V x)
    (J:smooth_compact_set hNX V) (B:set X):
  B `<=` V->
  (forall E:smooth_compact_set hNX V,
    (forall x,smooth_compact_carrier J x->
      norm_domain_interior NX (smooth_compact_carrier E) x)->
    B `<=` smooth_compact_carrier E)->
  B `<=` smooth_compact_carrier J.
Proof.
move=>hBV hEvery x hx;apply:contrapT=>hOutside.
pose W:=V `\` [set x].
have hOpenV:@open XT V.
  rewrite openE=>y hy.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX V y).1 (hV y hy)).
have hClosedPoint:@closed XT [set x].
  exact:(compact_closed (@metric_hausdorff R XT) (@compact_set1 XT x)).
have hOpenW:@open XT W.
  exact:openI hOpenV (closed_openC hClosedPoint).
have hW:forall y,W y->norm_domain_interior NX W y.
  move=>y hy;apply:(@norm_domain_interior_neighbourhood R X NX hNX W y).2.
  rewrite openE in hOpenW;exact:hOpenW y hy.
have hJW:smooth_compact_carrier J `<=` W.
  move=>y hy;split;first exact:smooth_compact_in_domain J y hy.
  move=>he;change (y=x) in he;subst y;exact:hOutside hy.
pose JW:=@Build_smooth_compact_set R X NX hNX W
  (smooth_compact_carrier J) hJW (smooth_compact_is_compact J).
have[E hInside]:=smooth_compact_neighbourhood_exists hW JW.
pose EV:=@Build_smooth_compact_set R X NX hNX V
  (smooth_compact_carrier E)
  (fun y hy=>(smooth_compact_in_domain E y hy).1) (smooth_compact_is_compact E).
have hPoint:=hEvery EV hInside x hx.
have hNotPoint:~[set x] x:=(smooth_compact_in_domain E x hPoint).2.
exact:hNotPoint (erefl x).
Qed.
End SmoothCompactNeighbourhoods.
