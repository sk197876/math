(** Federer (1969), 4.1.7, pp. 357, 359:
    the original coordinate-oriented Lebesgue
    current is nonzero on every nonempty
    open domain. The actual top vector
    has mass one and the original
    constant-density map is injective. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates ExteriorGrading FiniteExteriorPowers
  CurrentCoefficientNorms EuclideanTopCurrentMass CurrentSpaces CurrentConstantDensity
  CurrentOpenConstantDensity CurrentConstantDensityUniqueness EuclideanFundamentalCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_top_current_vector_nonzero]:
    the original coordinate orientation is
    nonzero, supporting E^n and the
    primitive nonuniqueness in Federer 4.1.7,
    pp. 357, 359. Dimension zero
    retains the original scalar-unit convention. *)
Lemma euclidean_top_current_vector_nonzero (R:realType) (h2:(1+1:R)!=0) n:
  e_lambda (@coordinate_basis R n) (ord_tuple n)<>0.
Proof.
move=>hZero;have hUnit:=@euclidean_top_current_vector_mass_one R h2 n.
rewrite hZero (real_seminorm_zero (@current_vector_mass_real_norm R h2 n n).1) in hUnit.
have hNe:(1:R)!=0:=@oner_neq0 R.
by rewrite -hUnit eqxx in hNe.
Qed.

(** Source for [euclidean_fundamental_current_nonzero]:
    the actual whole-space E^n is
    nonzero, supporting the correction of
    the bare primitive uniqueness assertion in
    Federer 4.1.7, p. 359. *)
Theorem euclidean_fundamental_current_nonzero (R:realType) (h2:(1+1:R)!=0) n:
  @euclidean_fundamental_current R h2 n<>0.
Proof.
move=>hZero;apply:(@euclidean_top_current_vector_nonzero R h2 n).
apply:(@current_constant_density_injective R h2 n n).
change (@current_constant_density_map R h2 n n
  (e_lambda (@coordinate_basis R n) (ord_tuple n)) =
  @current_constant_density_map R h2 n n 0).
rewrite linear0;exact:hZero.
Qed.

(** Source for [euclidean_fundamental_current_open_nonzero]:
    E^n restricted to every nonempty
    original open U is nonzero,
    supporting the corrected uniqueness with
    agreement on U in Federer 4.1.7,
    p. 359. *)
Theorem euclidean_fundamental_current_open_nonzero (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x):
  (exists x,U x)->@euclidean_fundamental_current_open R h2 n U hU<>0.
Proof.
move=>hNonempty hZero;apply:(@euclidean_top_current_vector_nonzero R h2 n).
apply:(@current_open_constant_density_injective R h2 n n U hU hNonempty).
change (@current_open_constant_density R h2 n n U hU
  (e_lambda (@coordinate_basis R n) (ord_tuple n)) =
  @current_open_constant_density R h2 n n U hU 0).
rewrite linear0;exact:hZero.
Qed.
