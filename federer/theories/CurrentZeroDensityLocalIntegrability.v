(** Federer (1969), 4.1.27, p. 384:
    the degenerate density is the actual
    zero field. Its local summability needs
    no ambient Radon or local-finiteness premise.
    Reuse the earlier constant measurability and
    zero integral laws through the current-density interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentCoefficientNorms CurrentDensityUP CurrentSummableDensityLocal
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableTotalBasic
  MeasureIntegralUP SummableRealFunctionUP
  LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_zero_density_locally_integrable]: the original
    zero-density case of 4.1.27,
    p. 384, under exactly the old
    measurable-open-set input of the density current
    of 4.1.7, p. 356. No
    finite ambient measure is required. *)
Theorem current_zero_density_locally_integrable (R:realType) (h2:(1+1:R)!=0) n m
    (gamma:set (R_n R n)->\bar R) (hGamma:is_measure gamma)
    (hBorel:@is_current_density_borel_measure R n gamma):
  @is_locally_integrable_current_density R h2 n m gamma
    (fun _=>0:exterior_power (R_n R n) m).
Proof.
pose X:=R_n R n.
pose V:=exterior_power X m.
pose N:=@current_vector_mass R h2 n m.
pose hN:=@current_vector_mass_real_norm R h2 n m.
have hMeas:=@measurable_total_constant R X (real_norm_metric_space hN) gamma hGamma 0.
have hZero:(fun _:X=>N (0:V))=(fun _=>0:R).
  apply:funext=>x;exact:real_seminorm_zero hN.1.
have hIntegral:is_measure_integral gamma (real_total_integrand (fun _:X=>N (0:V))) (0:R)%:E.
  rewrite hZero;exact:real_total_zero_integral hGamma.
exact:(@current_summable_density_locally_integrable R h2 n m gamma hGamma hBorel
  (fun _=>0:V) 0 hMeas hIntegral).
Qed.
