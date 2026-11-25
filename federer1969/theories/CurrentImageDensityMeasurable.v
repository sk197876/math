(** Federer (1969), 4.1.7, p. 359:
    the exterior differential image of the
    original weak unit density is measurable
    and bounded on compact subsets of U.
    Pullbacks of constant covectors give its
    actual finite coordinates; no regularity of
    the original density is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingIsomorphism
  AlternatingPairing CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces
  CurrentMultivectorDual CurrentConstantFields SmoothFormPullbackSealed CurrentImageDensityPairing
  CurrentUnitSmoothPairing FiniteCoordinateMeasurability LinearBasis FiniteDualDimension
  OpenFamilyTopologyMathcomp PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP
  SummableRealFunctionUP SummableRealNormed TotalScalarMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentImageDensityMeasurable.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation UT := (current_domain R v U).
Local Notation Z := (exterior_power Y m).
Local Notation ZN := (@current_vector_mass R h2 n m).
Local Notation hZN := (@current_vector_mass_real_norm R h2 n m).
Local Notation F := (@current_smooth_space R h2 v U hU m).
Local Notation fv := (@current_smooth_value R h2 v U hU m).
Local Notation pull := (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf).
Variable xi:UT->exterior_power X m.
Hypothesis hUnit:forall x,@current_vector_mass R h2 v m (xi x)<=1.
Local Notation image := (@current_image_density R v n m U f xi).

(** Source for [current_image_density_coordinate_field]:
    a target basis coordinate is paired
    with an actual smooth pulled-back constant
    covector, supporting the weight in Federer
    4.1.7, p. 359. *)
Lemma current_image_density_coordinate_field d (b:'I_d->Z) (hb:is_basis b) i:
  exists psi:F,forall x:UT,dual_basis hb i (image x)=pairing (xi x) (fv psi (set_val x)).
Proof.
exists (pull (@current_constant_form R h2 n V hV m (hom_to_form (dual_basis hb i))))=>x.
have h:=@current_image_density_constant_pairing R h2 v n m U V hU hV f hImage hf
  xi (hom_to_form (dual_basis hb i)) x.
by rewrite /pairing hom_to_formK in h.
Qed.

(** Source for [current_image_density_measurable]:
    the original Lambda_m Df(x)(xi(x)) is
    measurable in the actual target mass-norm
    topology, supporting Federer 4.1.7, p. 359.
    The original source and target dimensions
    and exterior degree can all be zero. *)
Theorem current_image_density_measurable
    (mu:set UT->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R v m).1)))->
  is_measure_measurable_function mu (partial_function_total (fun x=>(image x:real_norm_metric_space hZN))).
Proof.
move=>hXi.
have [d [b hb]]:=@current_vector_finite_basis R h2 n m.
apply:(@finite_coordinate_field_measurable R UT Z ZN hZN d b hb mu hm image)=>i.
have [psi hValues]:=current_image_density_coordinate_field hb i.
have hM:=@current_unit_smooth_pairing_measurable R h2 v m U hU xi hUnit mu hm hr hXi psi.
have hEqual:(fun x:UT=>pairing (xi x) (fv psi (set_val x)))=
    (fun x=>dual_basis hb i (image x)) by apply:funext=>x;exact:esym (hValues x).
rewrite hEqual in hM.
exact:(total_scalar_real_measurable hm (real_integrand_measurable_scalar_norm hm hM)).
Qed.

(** Source for [current_image_density_compact_bound]:
    the exact image density has a finite
    mass bound on each compact source set,
    supporting the Radon weight in Federer
    4.1.7, p. 359. This auxiliary bound
    does not normalize or replace the printed
    pointwise weight. *)
Theorem current_image_density_compact_bound (K:set UT):compact K->
  exists C:R,0<=C /\forall x,K x->ZN (image x)<=C.
Proof.
move=>hK.
have [d [b hb]]:=@current_vector_finite_basis R h2 n m.
have hEach i:exists M:R,0<=M /\forall x,K x->`|dual_basis hb i (image x)|<=M.
  have [psi hValues]:=current_image_density_coordinate_field hb i.
  have [M [hM hBound]]:=@current_unit_smooth_pairing_compact_bound R h2 v m U hU
    xi hUnit psi K hK.
  exists M;split;first exact:hM.
  by move=>x hx;rewrite hValues;exact:hBound x hx.
have [M hM]:=choice hEach.
exists (\sum_i M i*ZN (b i));split.
- apply:sumr_ge0=>i _;exact:(mulr_ge0 (hM i).1 (real_seminorm_nonnegative hZN.1 (b i))).
- exact:(@finite_coordinate_field_bound R UT Z ZN hZN d b hb image K M
    (fun i=>(hM i).1) (fun i x hx=>(hM i).2 x hx)).
Qed.
End CurrentImageDensityMeasurable.
