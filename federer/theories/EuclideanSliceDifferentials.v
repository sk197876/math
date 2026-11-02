(** Federer (1969), 3.2.10, p. 248: the maps v_y(z)=v(y,z)
    and their actual differentials. These supporting slice laws
    follow directly from the linear block inclusion and the
    first-order definition in 3.1.1, pp. 209–210. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanBlockLinearMaps EuclideanBlockNorms NormDifferentialUP
  NormDifferentialLinear LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_fixed_first_block_increment]: the
    last-coordinate direction in the diagram of Federer 3.2.10,
    p. 248. Supporting affine increment identity, including empty blocks. *)
Lemma euclidean_fixed_first_block_increment (R:realType) n k
    (y:R_n R n) (z h:R_n R k):
  euclidean_block_join (y,z+h)=euclidean_block_join (y,z)+
    @euclidean_last_injection R n k h.
Proof.
have hEq:((y,z)+((0:R_n R n),h))=(y,z+h).
  change ((y+0,z+h)=(y,z+h)); by rewrite addr0.
have hh:=@euclidean_block_join_linear R n k 1 (y,z) ((0:R_n R n),h).
rewrite !scale1r hEq in hh; exact hh.
Qed.

(** Source for [euclidean_fixed_first_block_distance]: the
    slice inclusion in Federer 3.2.10, p. 248, is isometric;
    this supports using the same global Lipschitz bound for v_y. *)
Lemma euclidean_fixed_first_block_distance (R:realType) n k
    (y:inner_metric_space (@euclidean_inner_productP R n))
    (z w:inner_metric_space (@euclidean_inner_productP R k)):
  mdist (euclidean_block_join (y,z)) (euclidean_block_join (y,w))=mdist z w.
Proof.
rewrite !inner_metric_distanceE.
have he:euclidean_block_join (y,z)-euclidean_block_join (y,w)=
    @euclidean_last_injection R n k (z-w).
  have h:=euclidean_fixed_first_block_increment y w (z-w).
  rewrite addrC subrK in h.
  by rewrite h addrAC subrr add0r.
by rewrite he euclidean_last_injection_norm.
Qed.

(** Source for [euclidean_slice_lipschitz]: the v_y maps
    in Federer 3.2.10, p. 248, are globally Lipschitz with
    the given bound of v. No injectivity outside the projected
    fibre and no differentiability hypothesis are required. *)
Lemma euclidean_slice_lipschitz (R:realType) m n k
    (v:inner_metric_space (@euclidean_inner_productP R (n+k))->
      inner_metric_space (@euclidean_inner_productP R m)):
  is_metric_lipschitz setT v ->forall y,
    is_metric_lipschitz setT (fun z=>v (euclidean_block_join (y,z))).
Proof.
move=>[L [hL hBound]] y; exists L; split; first exact hL.
split; first exact hBound.1.
move=>z w _ _; have h:=hBound.2 (euclidean_block_join (y,z))
  (euclidean_block_join (y,w)) Logic.I Logic.I.
by rewrite euclidean_fixed_first_block_distance in h.
Qed.

(** Source for [euclidean_slice_differential]: L_x=Dv_y(z)
    in Federer 3.2.10, p. 248. At every actual
    differentiability point of v, the slice differential is
    Dv composed with the last-block inclusion. No value is
    assigned at points where the full differential does not exist. *)
Lemma euclidean_slice_differential (R:realType) m n k
    (v:R_n R (n+k)->R_n R m) (y:R_n R n) (z:R_n R k)
    (M:Hom (R_n R (n+k)) (R_n R m)):
  has_norm_differential (inner_norm (@euclidean_inner_productP R (n+k)))
    (inner_norm (@euclidean_inner_productP R m)) setT v (euclidean_block_join (y,z)) M ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R k))
    (inner_norm (@euclidean_inner_productP R m)) setT
    (fun w=>v (euclidean_block_join (y,w))) z
    (hom_comp M (@euclidean_last_injection_map R n k)).
Proof.
move=>hV; pose j:=@euclidean_last_injection_map R n k.
have hJ:norm_bounded_linear (inner_norm (@euclidean_inner_productP R k))
    (inner_norm (@euclidean_inner_productP R (n+k))) j.
  exists 1; split; first exact:ler01.
  move=>h; change (is_true (inner_norm (@euclidean_inner_productP R (n+k))
    (@euclidean_last_injection R n k h)<=1*inner_norm (@euclidean_inner_productP R k) h)).
  by rewrite euclidean_last_injection_norm mul1r.
constructor.
- exists 1; split; first exact:ltr01; by move=>h hh.
- exact (norm_bounded_linear_compose hJ (norm_differential_bounded hV)).
- move=>e he; have [d [hd hRem]]:=norm_differential_remainder hV he.
  exists d; split; first exact hd.
  move=>h _ hh.
  have hSmall:inner_norm (@euclidean_inner_productP R (n+k))
      (@euclidean_last_injection R n k h)<d.
    by rewrite euclidean_last_injection_norm.
  have hR:=hRem (@euclidean_last_injection R n k h) Logic.I hSmall.
  rewrite euclidean_last_injection_norm in hR.
  rewrite euclidean_fixed_first_block_increment.
  exact hR.
Qed.
