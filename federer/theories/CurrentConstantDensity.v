(** Federer (1969), 4.1.7, pp. 356–357: constant
    Lebesgue-density currents have zero directional
    derivatives. Reuse the original constant-field
    differential and distribution integration by parts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormClassOneUP
  NormClassOneLinear NormClassZeroArithmetic InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentCoefficientNorms CurrentSpaces CurrentDensityUP
  CurrentDensityAction CurrentDensityUniqueness CurrentDensityArithmetic CurrentLebesgueDensity
  CurrentDirectionalDerivative EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentConstantDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation mu := (@euclidean_lebesgue_measure R n).

(** Source for [current_constant_density]: the original
    constant Lebesgue-density current, supporting
    E^n and the constancy theorem in Federer
    4.1.7, pp. 356–357. *)
Definition current_constant_density (a:V):@full_current_space R h2 n m:=
  @current_lebesgue_density R h2 n m (fun _=>a)
    (@continuous_current_density_integrable R h2 n m (fun _=>a)
      (@norm_class_zero_constant R X V NX VN hVN (fun _=>True) a hFull)).

(** Source for [current_constant_density_action]: the
    original integral of the pairing with a
    constant multivector, supporting Federer 4.1.7,
    pp. 356–357. *)
Theorem current_constant_density_action a:
  is_current_density_action mu (fun _=>a) (current_constant_density a).
Proof. exact:current_lebesgue_density_action. Qed.

(** Source for [current_constant_density_linear]: the
    original constant-density current is linear in
    its multivector, supporting the constancy theorem
    of Federer 4.1.7, p. 357. *)
Theorem current_constant_density_linear:linear current_constant_density.
Proof.
move=>c a b.
apply:(@current_density_action_unique R h2 n m mu (fun _=>c*:a+b)).
- exact:current_constant_density_action.
- apply:(@current_density_sum_action R h2 n m mu (euclidean_lebesgue_is_measure R n)
    (fun _=>c*:a) (fun _=>b) (c*:current_constant_density a) (current_constant_density b)).
  + exact:(@current_density_scaled_action R h2 n m mu (euclidean_lebesgue_is_measure R n)
      (fun _=>a) (current_constant_density a) c (current_constant_density_action a)).
  + exact:current_constant_density_action.
Qed.

(** Source for [current_constant_density_map]: the
    original linear inclusion of constant
    Lebesgue densities as currents, supporting
    Federer 4.1.7, p. 357. *)
Definition current_constant_density_map:Hom V (@full_current_space R h2 n m):=
  @HomMap R V (@full_current_space R h2 n m) current_constant_density
    (introT (asboolP _) current_constant_density_linear).

(** Source for [current_constant_density_directional_zero]:
    every D_v of a constant Lebesgue-density
    current vanishes, supporting D_j E^n=0 in
    Federer 4.1.7, p. 357. *)
Theorem current_constant_density_directional_zero a v:
  @current_directional_derivative R h2 n m (fun _=>True) hFull v
    (current_constant_density a)=0.
Proof.
have hC1:=@norm_class_one_constant_field R X V NX VN hNX hVN
  (fun _=>True) a hFull.
have hAction:=@current_lebesgue_directional_action R h2 n m (fun _=>a)
  (fun _=>0) v (current_constant_density a) (current_constant_density_action a) hC1.
have hZero:(fun x:X=>(0:Hom X V) v)=(fun _=>0:V).
  apply:funext=>x;exact:hom_zeroE.
rewrite hZero in hAction.
exact:(@current_density_action_unique R h2 n m mu (fun _=>0)
  _ _ hAction (@current_density_zero_action R h2 n m mu (euclidean_lebesgue_is_measure R n))).
Qed.
End CurrentConstantDensity.
