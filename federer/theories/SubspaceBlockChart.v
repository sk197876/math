(** Federer (1969), 3.1.19, p. 231: existence of adapted linear
    coordinates for the plane in condition (1), by extending its
    basis as in 1.6.1 and using the dual coordinates of 1.6.3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceSums
  SubspaceCarrier GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates
  LinearBasis FiniteDualDimension Annihilator FiniteIndependence FiniteBasisComparison
  BasisInterpolation SimpleAdaptedBasis EuclideanBlockLinearMaps SubspaceBlockChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [subspace_block_chart_exists]: supporting the
    linear coordinate change for (1) implies (2) and (4) in
    Federer 3.1.19, p. 231. The actual mu-plane is the kernel of
    the last-coordinate map after an invertible change of basis. *)
Theorem subspace_block_chart_exists (R:realType) mu l (Z:G (R_n R (mu+l)) mu) :
  exists beta gamma, is_subspace_block_chart (grassmann_val Z) beta gamma.
Proof.
pose X:=R_n R (mu+l).
have [w hw]:=grassmann_proof Z.
have hi:=@finite_independent_map R (Finite.clone 'I_mu _)
  (subspace_space (grassmann_val Z)) X (subspace_inclusion (grassmann_val Z)) w
  (@subspace_val_injective R X (grassmann_val Z)) (finite_basis_independent hw).
pose hmn:=leq_addr l mu.
have [e [he hew]]:=@finite_basis_extension_fixed R X mu (mu+l)
  (fun i=>subspace_val (w i)) (@coordinate_basis R (mu+l)) hmn hi (@coordinate_basisP R (mu+l)).
have hleft i:e (lshift l i)=subspace_val (w i).
  have heq:lshift l i=widen_ord hmn i by apply: val_inj.
  by rewrite heq hew.
pose beta0:=fun x:X=>[ffun i=>dual_basis he i x]:X.
have hbeta:linear beta0.
  move=>c x y; apply/ffunP=>i; by rewrite /beta0 !ffunE linearP.
pose beta:=@HomMap R X X beta0 (introT (asboolP _) hbeta).
pose gamma:=hom_of_linear (basis_interpolation (@coordinate_basisP R (mu+l)) e).
have hgb:cancel gamma beta.
  apply: (@basis_linear_ext R (Choice.clone 'I_(mu+l) _) X (@coordinate_basis R (mu+l))
    (@coordinate_basisP R (mu+l)) X
    (linear_comp (hom_as_linear beta) (hom_as_linear gamma)) (linear_id X)).
  move=>i; change (beta0 (basis_interpolation (@coordinate_basisP R (mu+l)) e (@coordinate_basis R (mu+l) i))=
    @coordinate_basis R (mu+l) i).
  rewrite basis_interpolationE; apply/ffunP=>j.
  by rewrite /beta0 /coordinate_basis !ffunE dual_basisE eq_sym.
have hbg:cancel beta gamma.
  apply: (@basis_linear_ext R (Choice.clone 'I_(mu+l) _) X e he X
    (linear_comp (hom_as_linear gamma) (hom_as_linear beta)) (linear_id X)).
  move=>i; change (gamma (beta0 (e i))=e i).
  have hb:beta0 (e i)=@coordinate_basis R (mu+l) i.
    apply/ffunP=>j; by rewrite /beta0 /coordinate_basis !ffunE dual_basisE eq_sym.
  by rewrite hb /gamma hom_of_linearE basis_interpolationE.
have hdual x i:grassmann_val Z x -> dual_basis he (rshift mu i) x=0.
  move=>hx.
  have hh:=congr1 subspace_val (basis_vector_expansion hw (subspace_lift hx)).
  rewrite subspace_liftE linear_sum in hh.
  rewrite hh linear_sum; apply: big1=>j _.
  change (dual_basis he (rshift mu i)
    ((dual_basis hw j (subspace_lift hx):R) *: subspace_val (w j))=0).
  rewrite (linZ (hom_linear (dual_basis he (rshift mu i)))).
  change ((dual_basis hw j (subspace_lift hx):R) *
    dual_basis he (rshift mu i) (subspace_val (w j))=0).
  by rewrite -hleft dual_basisE eq_lrshift mulr0.
have hplane x:grassmann_val Z x <-> @euclidean_last_block_map R mu l (beta x)=0.
  split.
  - move=>hx; apply/ffunP=>i.
    by rewrite /euclidean_last_block_map /= /euclidean_last_block /beta0 !ffunE hdual.
  - move=>hx; rewrite (basis_vector_expansion he x).
    apply: big_ind; [exact: subspace_zero|move=>u v; exact: subspace_add|move=>i _].
    case: (split_ordP i)=>[j ->|j ->].
    + apply: subspace_scale; rewrite hleft; exact: subspace_valP.
    + have hz:dual_basis he (rshift mu j) x=0.
        have hh:=congr1 (fun z:R_n R l=>z j) hx.
        by move: hh; rewrite /euclidean_last_block_map /= /euclidean_last_block /beta0 !ffunE.
      rewrite hz scale0r; exact: subspace_zero.
exists beta,gamma; by constructor.
Qed.
