(** Federer (1969), 2.7.16, printed p. 140, example (7): "If X is the space
    of all m dimensional affine subspaces of R^n, and p in O*(n, n - m) ...
    Since im p* = im(p* o p) is the orthogonal complement of ker p,
    p^{-1}{y} = tau_{p*(y)} ker p whenever y in R^{n-m}, tau_z ker p =
    tau_{(p* o p) z} ker p whenever z in R^n." Here p is a member of O*(n, n
    - m) = orthogonal_projections of OrthogonalInjectionSpaces.v (the
    adjoints of orthogonal injections of R^{n-m} into R^n, 1.7.4, p. 30),
    with m <= n, and p* is its adjoint, an orthogonal injection with p o p*
    = 1. The module proves that ker p is m dimensional, so that the fibres
    p^{-1}{y} are points of the space X of AffineSubspaceSpace.v: an
    orthonormal basis of im p* extends to an orthonormal basis of R^n
    (1.7.3, p. 30); the m added vectors lie in ker p and span it. It then
    proves the displayed identities. The local erratum has no entry for p.
    140. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm LinearBasis Bilinear TensorUP Hom
  HomInner ModuleQuotient GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  CoordinateProjection
  OrthogonalMaps OrthonormalFamilies OrthonormalFrameMap OrthonormalCapacityExtension FiniteBasisComparison
  AdjointUP AdjointLaws HomSpaceTopology OrthogonalInjectionSpaces GrassmannHomogeneousSpace
  AffineSubspaceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProjectionFibres.
Variable R : realType.
Variables n m : nat.
Hypothesis hmn : (m <= n)%N.
Local Notation k := (n - m)%N.
Local Notation Vn := (R_n R n).
Local Notation Vk := (R_n R k).
Local Notation Vm := (R_n R m).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bk := (@euclidean_inner_product R k).
Local Notation Bm := (@euclidean_inner_product R m).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation eps := (@coordinate_basis R _).
Local Notation OP := (set_type (orthogonal_projections hBk hBn hbn)).
Local Notation pm := (@orthogonal_projection_map R Vk Vn Bk Bn hBk hBn n _ hbn).

(** Source for [projection_adjoint]: the adjoint p* of p in
    O*(n, n - m), an orthogonal injection of R^{n-m} into R^n, Federer
    1.7.4, p. 30, as used in 2.7.16, p. 140. Definition by choice; later
    results use only projection_adjoint_orthogonal and
    projection_adjointE. *)
Definition projection_adjoint (q : OP) : {linear Vk -> Vn} :=
  projT1 (cid (orthogonal_projection_map_projection q)).

(** Source for [projection_adjoint_orthogonal]: p* is an orthogonal
    injection, Federer 1.7.4, p. 30. Specification of
    projection_adjoint. *)
Lemma projection_adjoint_orthogonal (q : OP) x y :
  Bn (projection_adjoint q x) (projection_adjoint q y) = Bk x y.
Proof. exact: (projT2 (cid (orthogonal_projection_map_projection q))).1. Qed.

(** Source for [projection_adjointE]: y . p(v) = p*(y) . v, Federer
    1.7.4, p. 30. Specification of projection_adjoint. *)
Lemma projection_adjointE (q : OP) y v : Bk y (pm q v) = Bn (projection_adjoint q y) v.
Proof. exact: (projT2 (cid (orthogonal_projection_map_projection q))).2. Qed.

(** Source for [projection_adjointK]: p o p* = 1_{R^{n-m}}, Federer
    1.7.4, p. 30. Supporting lemma. *)
Lemma projection_adjointK (q : OP) y : pm q (projection_adjoint q y) = y.
Proof.
apply: (inner_vectors_ext hBk)=> z.
by rewrite projection_adjointE projection_adjoint_orthogonal.
Qed.

(** Source for [projection_adjoint_perp]: im p* is perpendicular to
    ker p, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma projection_adjoint_perp (q : OP) y v : pm q v = 0 -> Bn (projection_adjoint q y) v = 0.
Proof. by move=> hv; rewrite -projection_adjointE hv; exact: (bil0r (inner_bilinear hBk)). Qed.

(** Source for [projection_residual_kernel]: v - p*(p(v)) belongs to
    ker p, Federer 2.7.16, p. 140 ("im p* = im(p* o p) is the orthogonal
    complement of ker p"). Supporting lemma. *)
Lemma projection_residual_kernel (q : OP) v : pm q (v - projection_adjoint q (pm q v)) = 0.
Proof.
rewrite (linearB (hom_as_linear (pm q))) /=.
by rewrite (projection_adjointK q (pm q v)) subrr.
Qed.

(** Source for [projection_kernel_exists]: ker p is m dimensional for p
    in O*(n, n - m), presupposed in Federer 2.7.16, p. 140 ("p^{-1}{y}
    is an m dimensional affine subspace"). Proof supplied: the
    orthonormal family p*(e_1), ..., p*(e_{n-m}) extends to an
    orthonormal basis d of R^n (1.7.3, p. 30); the m added vectors are
    orthogonal to im p*, hence lie in ker p, and a vector of ker p
    minus its orthonormal expansion in them is orthogonal to the whole
    basis d, hence 0. *)
Lemma projection_kernel_exists (q : OP) : exists K : G Vn m, forall v, grassmann_val K v <-> pm q v = 0.
Proof.
pose h := projection_adjoint q.
have hkn : (k <= n)%N := leq_subr m n.
have hfam : orthonormal_family Bn (fun i : 'I_k => h (eps i)).
  move=> i j; rewrite projection_adjoint_orthogonal euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite eq_sym.
have [d [hd hdw]] := orthonormal_capacity_extension hBn (finite_basis_independent hbn) hfam hkn.
have hidx (j : 'I_m) : (k + j < n)%N.
  by rewrite -[X in (_ < X)%N](subnK hmn) ltn_add2l.
pose idx (j : 'I_m) : 'I_n := Ordinal (hidx j).
pose f (j : 'I_m) : Vn := d (idx j).
have hf : orthonormal_family Bn f.
  move=> i j; rewrite /f hd; congr (if _ then _ else _).
  apply/eqP/eqP=> [he|->] //; apply: val_inj.
  by have := congr1 val he; rewrite /= => /addnI.
have hperp (i : 'I_k) (j : 'I_m) : Bn (h (eps i)) (f j) = 0.
  rewrite -(hdw i) /f hd; case: eqP=> // he.
  have := congr1 val he; rewrite /= => hv.
  by have := ltn_ord i; rewrite hv -ltn_subRL subnn ltn0.
have hpf (j : 'I_m) : pm q (f j) = 0.
  apply: (inner_vectors_ext hBk)=> z; rewrite projection_adjointE (bil0r (inner_bilinear hBk)).
  pose P := fun z : Vk => Bn (h z) (f j) = 0.
  apply: (basis_induction hbk (P := P)).
  - by rewrite /P linear0 (bil0l (inner_bilinear hBn)).
  - by move=> x y; rewrite /P linearD (bilDl (inner_bilinear hBn))=> -> ->; rewrite addr0.
  - by move=> a x; rewrite /P linearZ (bilZl (inner_bilinear hBn))=> ->; rewrite scaler0.
  - by move=> i; exact: hperp.
have [kk [hkk hkkf]] := orthonormal_frame_map_exists hBn hf.
have hkki : injective kk := orthogonal_map_injective hBm hBn hkk.
exists (linear_image_grassmann hbm hkki)=> v; rewrite linear_image_grassmannE; split.
- move=> [u <-]; pose P := fun u : Vm => pm q (kk u) = 0.
  apply: (basis_induction hbm (P := P)).
  + by rewrite /P !linear0.
  + by move=> x y; rewrite /P !linearD /= => -> ->; rewrite addr0.
  + by move=> a x; rewrite /P !linearZ /= => ->; rewrite scaler0.
  + by move=> j; rewrite /P hkkf; exact: hpf.
- move=> hv; pose u : Vm := [ffun j => Bn v (f j)]; exists u.
  pose w := v - kk u.
  have hwf (j : 'I_m) : Bn (d (idx j)) w = 0.
    rewrite /w (bilBr (inner_bilinear hBn)).
    have -> : Bn (d (idx j)) (kk u) = u j.
      rewrite -/(f j) -hkkf hkk (inner_symmetric hBm) euclidean_inner_basis.
      by [].
    by rewrite /u ffunE (inner_symmetric hBn) subrr.
  have hpw : pm q w = 0.
    rewrite /w (linearB (hom_as_linear (pm q))) /= hv sub0r.
    have -> : pm q (kk u) = 0.
      pose P := fun u : Vm => pm q (kk u) = 0.
      apply: (basis_induction hbm (P := P)).
      + by rewrite /P !linear0.
      + by move=> x y; rewrite /P !linearD /= => -> ->; rewrite addr0.
      + by move=> a x; rewrite /P !linearZ /= => ->; rewrite scaler0.
      + by move=> j; rewrite /P hkkf; exact: hpf.
    by rewrite oppr0.
  have hwh (i : 'I_k) : Bn (d (widen_ord hkn i)) w = 0.
    by rewrite hdw; exact: projection_adjoint_perp.
  have hall (i : 'I_n) : Bn (d i) w = 0.
    case: (ltnP i k)=> hi.
    + have -> : i = widen_ord hkn (Ordinal hi) by apply: val_inj.
      exact: hwh.
    + have hj : (i - k < m)%N.
        by rewrite ltn_subLR // (subnK hmn) ltn_ord.
      have -> : i = idx (Ordinal hj) by apply: val_inj; rewrite /= subnKC.
      exact: hwf.
  have hdb := orthonormal_family_full_basis hBn hbn hd.
  have hzero : forall x, Bn x w = 0.
    apply: (basis_induction hdb (P := fun x => Bn x w = 0)).
    + exact: (bil0l (inner_bilinear hBn)).
    + by move=> x y hx hy; rewrite (bilDl (inner_bilinear hBn)) hx hy addr0.
    + by move=> a x hx; rewrite (bilZl (inner_bilinear hBn)) hx scaler0.
    + exact: hall.
  have hw0 : w = 0 by apply/eqP; rewrite -(inner_self_eq0 hBn); apply/eqP; exact: hzero.
  by apply/eqP; rewrite eq_sym -subr_eq0; apply/eqP.
Qed.

(** Source for [projection_kernel]: ker p as a member of G(n, m),
    Federer 2.7.16, p. 140. Definition by choice; later results use only
    projection_kernelE. *)
Definition projection_kernel (q : OP) : G Vn m := projT1 (cid (projection_kernel_exists q)).

(** Source for [projection_kernelE]: v belongs to ker p if and only if
    p(v) = 0, Federer 2.7.16, p. 140. Specification of
    projection_kernel. *)
Lemma projection_kernelE (q : OP) v : grassmann_val (projection_kernel q) v <-> pm q v = 0.
Proof. exact: (projT2 (cid (projection_kernel_exists q))). Qed.

(** Source for [projection_adjoint_image]: "im p* = im(p* o p) is the
    orthogonal complement of ker p", Federer 2.7.16, p. 140: for v in
    R^n, v = p*(y) for some y if and only if v is perpendicular to
    ker p, if and only if p*(p(v)) = v. Direct formalisation. *)
Theorem projection_adjoint_image (q : OP) (v : Vn) :
  [/\ (exists y, projection_adjoint q y = v) <-> (forall w, pm q w = 0 -> Bn v w = 0),
      (exists y, projection_adjoint q y = v) <-> projection_adjoint q (pm q v) = v &
      (forall z, (exists y, projection_adjoint q (pm q z) = projection_adjoint q y))].
Proof.
have h1 : (exists y, projection_adjoint q y = v) -> projection_adjoint q (pm q v) = v.
  by move=> [y <-]; rewrite projection_adjointK.
have h2 : (forall w, pm q w = 0 -> Bn v w = 0) -> projection_adjoint q (pm q v) = v.
  move=> hp; set r := v - projection_adjoint q (pm q v).
  have hr : pm q r = 0 := projection_residual_kernel q v.
  have hrr : Bn r r = 0.
    rewrite {1}/r (bilBl (inner_bilinear hBn)) (hp _ hr) (projection_adjoint_perp _ hr).
    by rewrite subrr.
  have : r = 0 by apply/eqP; rewrite -(inner_self_eq0 hBn); exact/eqP.
  by move/eqP; rewrite subr_eq0=> /eqP.
split.
- split; first by move=> [y <-] w hw; exact: projection_adjoint_perp.
  by move=> hp; exists (pm q v); exact: h2 hp.
- by split=> // h; exists (pm q v).
- by move=> z; exists (pm q z).
Qed.

(** Source for [projection_fibre]: the fibre p^{-1}{y} = tau_{p*(y)} ker p
    as a point of the space X of m dimensional affine subspaces of R^n,
    Federer 2.7.16, p. 140. Definition. *)
Definition projection_fibre (q : OP) (y : Vk) : affine_subspace_carrier Vn m :=
  affine_subspace_of (projection_adjoint q y) (projection_kernel q).

(** Source for [projection_fibreE]: "p^{-1}{y} = tau_{p*(y)} ker p
    whenever y in R^{n-m}", Federer 2.7.16, p. 140: x belongs to
    tau_{p*(y)} ker p if and only if p(x) = y. Direct formalisation. *)
Theorem projection_fibreE (q : OP) (y : Vk) x : affine_points (projection_fibre q y) x <-> pm q x = y.
Proof.
rewrite /projection_fibre affine_subspace_of_points /affine_coset /= projection_kernelE.
rewrite (linearB (hom_as_linear (pm q))) /= projection_adjointK.
by split=> [/eqP|->]; [rewrite subr_eq0=> /eqP|rewrite subrr].
Qed.

(** Source for [projection_kernel_translate]: "tau_z ker p =
    tau_{(p* o p) z} ker p whenever z in R^n", Federer 2.7.16, p. 140.
    Direct formalisation. *)
Theorem projection_kernel_translate (q : OP) (z : Vn) :
  affine_coset z (projection_kernel q) = affine_coset (projection_adjoint q (pm q z)) (projection_kernel q).
Proof.
apply: affine_coset_move; rewrite /affine_coset /= projection_kernelE.
rewrite (linearB (hom_as_linear (pm q))) /= projection_adjointK; exact: subrr.
Qed.

(** Source for [projection_fibre_direction]: dir p^{-1}{y} = ker p,
    Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma projection_fibre_direction (q : OP) y : affine_direction (projection_fibre q y) = projection_kernel q.
Proof. exact: affine_subspace_of_direction. Qed.

(** Source for [projection_fibre_nearest]: the point of p^{-1}{y} nearest
    to 0 is p*(y), Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma projection_fibre_nearest (q : OP) y :
  affine_nearest hBm hBn hbm (projection_fibre q y) = projection_adjoint q y.
Proof.
apply: esym; apply: affine_nearest_unique.
- by apply/projection_fibreE; exact: projection_adjointK.
- move=> w; rewrite projection_fibre_direction projection_kernelE.
  exact: projection_adjoint_perp.
Qed.

End ProjectionFibres.

Arguments projection_adjoint {R n m} q.
Arguments projection_kernel {R n m} hmn q.
Arguments projection_fibre {R n m} hmn q y.
