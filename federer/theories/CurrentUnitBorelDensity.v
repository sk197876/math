(** Federer (1969), 4.1.7, pp. 357–358:
    use Borel representatives of the normalized
    variation density when comparing measures.
    Lusin's corollary supplies the representative;
    the actual closed unit mass ball preserves
    the global norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionBasic RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentCoefficientNorms
  CurrentMultivectorDual CurrentDensityBorelVersion OpenFamilyTopologyMathcomp
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP RadonMeasureUP
  BorelFunctionUP BorelFunctionBasic BorelContinuousRegion TopologicalBorel MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_unit_density_borel_version]:
    the original unit-bounded multivector density
    has an almost equal Borel representative
    bounded by one everywhere, supporting Federer
    4.1.7, pp. 357–358, by 2.3.6,
    p. 77. No value of the maximal ball
    orienting field is changed by this auxiliary choice. *)
Theorem current_unit_density_borel_version (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (mu:set (current_domain R n U)->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (xi:current_domain R n U->exterior_power (R_n R n) m):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))) ->
  (forall x,@current_vector_mass R h2 n m (xi x)<=1) ->
  exists z:current_domain R n U->exterior_power (R_n R n) m,
    is_borel_function (fun x=>(z x:real_norm_metric_space (@current_vector_mass_real_norm R h2 n m))) /\
    (forall x,@current_vector_mass R h2 n m (z x)<=1) /\
    measure_almost_everywhere mu [set x|xi x=z x].
Proof.
move=>hXi hUnit.
pose V:=exterior_power (R_n R n) m.
pose VN:=@current_vector_mass R h2 n m.
pose hVN:=@current_vector_mass_real_norm R h2 n m.
pose VT:=real_norm_metric_space hVN.
have [z [hZ hAgree]]:=@current_density_borel_version R h2 n m U hU mu hm hr xi hXi.
pose D:set VT:=[set v|VN v<=1].
have hDClosed:closed D.
  have hEq:D=metric_closed_ball (0:VT) 1.
    apply:funext=>v; apply:propext.
    change (VN v<=1<->VN (0-v)<=1).
    have hNorm:VN (0-v)=VN v.
      rewrite sub0r;exact:(@real_seminorm_negate R V VN hVN.1 v).
    by rewrite hNorm.
  rewrite hEq; exact:metric_closed_ball_closed.
pose clip (v:VT):VT:=if pselect (D v) then v else 0.
have hClip:is_borel_function clip.
  exact:(@borel_continuous_region_extension VT VT D id 0
    (closed_borel_set hDClosed) (fun v _ P hP=>hP)).
pose w x:=clip (z x).
have hW:is_borel_function (fun x=>(w x:VT)).
  exact:(borel_function_composition hZ hClip).
have hWUnit x:VN (w x)<=1.
  rewrite /w /clip; case:pselect=>hx; first exact:hx.
  change (is_true (VN (0:V)<=1)).
  have hZero:VN (0:V)=0:=@real_seminorm_zero R V VN hVN.1.
  by rewrite hZero ler01.
exists w; split; first exact:hW.
split; first exact:hWUnit.
apply:(@measure_almost_everywhere_mono R (current_domain R n U) mu hm _ _ _ hAgree)=>x hx.
have hD:D (z x) by rewrite -hx; exact:hUnit.
change (xi x=clip (z x)); rewrite /clip; by case:pselect.
Qed.
