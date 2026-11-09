(** Federer (1969), 3.3.17, p. 300: the original
    infinite-radius cone is an actual Borel set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureProjectionCone StructureConeOpen
  TopologicalProductMaps TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_finite_cone_open]: supporting
    the regularisation in Federer 3.3.17, p. 300, using the
    actual joint cone openness proved in 3.3.2, p. 287.
    The centre, projection, finite radius and aperture are fixed. *)
Lemma structure_projection_finite_cone_open (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (r s:R):
  open (structure_cone (structure_projection_kernel hmn p) a r%:E s).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose F (x:X):=((a,p),x).
have hF:continuous F.
  apply:topological_pair_continuous; first exact:cst_continuous.
  by move=>x; exact:cvg_id.
exact:(open_comp (fun x _=>hF x) (@structure_cone_incidence_open R n m hmn r s)).
Qed.

(** Source for [structure_projection_infinite_cone_borel]: supporting
    actual Borel test for the regularisation of Federer 3.3.17,
    p. 300. The ORIGINAL infinite cone is the union of its
    original natural-radius open cones. No radius-zero ball or
    change to the strict radial convention is introduced. *)
Lemma structure_projection_infinite_cone_borel (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n)) (s:R):
  borel_set (structure_cone (structure_projection_kernel hmn p) a +oo s).
Proof.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose C k:=structure_cone (structure_projection_kernel hmn p) a (k%:R:R)%:E s.
have hUnion:structure_cone (structure_projection_kernel hmn p) a +oo s=\bigcup_k C k.
  apply/seteqP; split=>x.
  - move=>hx; have [hAngle hRadius]:=(@structure_projection_coneE R n m hmn p a +oo s x).1 hx.
    pose norm:=inner_norm (@euclidean_inner_productP R n) (x-a).
    have hBound:(norm<(Num.bound norm)%:R)%R by apply:archi_boundP; exact:inner_norm_nonnegative.
    exists (Num.bound norm); first exact:Logic.I.
    apply:(@structure_projection_coneE R n m hmn p a _ s x).2.
    split; first exact:hAngle.
    by rewrite lte_fin.
  - move=>[k _ hx]; have [hAngle hRadius]:=(@structure_projection_coneE R n m hmn p a _ s x).1 hx.
    apply:(@structure_projection_coneE R n m hmn p a +oo s x).2.
    split; first exact:hAngle.
    exact:ltry.
rewrite hUnion; apply:borel_set_countable_union (countableP _) _=>k _.
exact:open_borel_set (@structure_projection_finite_cone_open R n m hmn p a k%:R s).
Qed.
