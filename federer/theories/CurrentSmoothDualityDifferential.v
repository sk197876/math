(** Federer (1969), 4.1.7, p. 356:
    the left square of the original actual
    smooth diagram commutes with its printed
    sign. The proof applies the earlier exact
    divergence identity to the genuine first
    differential; it assumes no diagram law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormDifferentialLocal NormDifferentialDirectional InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms ExteriorHomogeneousProducts
  CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces CurrentDualityCoefficients CurrentSmoothDuality
  CurrentDegreeTransport SmoothCurrentExteriorDerivative SmoothCurrentDivergence
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws ExteriorDifferentialUP ExteriorDifferentialSealed
  DivergenceUP DivergenceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothDualityDifferential.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Hypothesis hp:(p.+1<=n)%N.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o (n-p.+1)).
Local Notation NY := (@current_form_comass R h2 n (n-p.+1)).
Local Notation hNY := (@current_form_comass_real_norm R h2 n (n-p.+1)).
Local Notation Z := (exterior_power X p.+1).
Local Notation NZ := (@current_vector_mass R h2 n p.+1).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n p.+1).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU (n-p.+1)).
Local Notation ev := (@current_smooth_value R h2 n U hU (n-p.+1)).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation vv := (fun m=>@current_vector_smooth_value R h2 n U hU m).
Local Notation hV := (fun m=>@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation upper := (@current_duality_upper_coefficient R h2 n p.+1 hp).
Local Notation up := (@current_smooth_duality_upper R h2 n p.+1 hp U hU).
Local Notation hp0 := (leq_trans (leqnSn p) hp).
Local Notation up0 := (@current_smooth_duality_upper R h2 n p hp0 U hU).
Local Notation div := (@smooth_current_divergence R h2 n p U hU).
Local Notation d := (@smooth_current_exterior_derivative R h2 n (n-p.+1) U hU).
Local Notation tr := (@current_smooth_degree_transport R h2 n U hU
  (n-p.+1).+1 (n-p) (subnSK hp)).

(** Source for [current_smooth_duality_divergence]:
    div composed with D^(n-p) equals
    D^(n-p+1) composed with (-1)^(n-p)d,
    the original left square in Federer
    4.1.7, p. 356. Input vector
    degree is p+1 and no negative
    output degree is introduced. *)
Theorem current_smooth_duality_divergence (phi:E):
  div (up phi)=(-1:R)^+(n-p.+1)*:up0 (tr (d phi)).
Proof.
apply:(smooth_function_extensional (hV p))=>x hx.
rewrite (@smooth_function_scale_value R X (exterior_power X p) NX
  (@current_vector_mass R h2 n p) hNX (@current_vector_mass_real_norm R h2 n p)
  U (V p) (vv p) (hV p))
  (@current_smooth_duality_upper_values R h2 n p hp0 U hU _ x hx)
  current_smooth_degree_transport_values.
have [L [hL hExterior]]:=@smooth_current_exterior_derivative_actual R h2 n (n-p.+1) U hU phi x hx.
have hPost:=@norm_differential_postcompose R X Y Z NX NY NZ hNX U (ev phi) x L upper
  hL (@current_duality_upper_bounded R h2 n p.+1 hp).
have hActual:has_norm_differential NX NZ U (vv p.+1 (up phi)) x (hom_comp upper L).
  apply:(@norm_differential_domain_agreement R X Z NX NZ hNX U
    (fun z=>upper (ev phi z)) (vv p.+1 (up phi)) x (hom_comp upper L) _ hPost)=>z hz.
  exact:esym (@current_smooth_duality_upper_values R h2 n p.+1 hp U hU phi z hz).
have [M [hM hDiv]]:=@smooth_current_divergence_actual R h2 n p U hU (up phi) x hx.
have hSame:=norm_differential_unique hNX hNZ hM hActual.
rewrite hSame in hDiv.
have hDivValue:=divergence_value_unique hDiv (@Divergence.laws R h2 n p (hom_comp upper L)).
have hExteriorValue:=exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n R^o (n-p.+1) L) hExterior.
rewrite hDivValue (@current_upper_duality_divergence_algebra R h2 n p hp L) hExteriorValue;by [].
Qed.
End CurrentSmoothDualityDifferential.
