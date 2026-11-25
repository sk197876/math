(** Federer (1969), 3.4.12, pp. 338–339:
    complex multilinearity is retained under original operator
    norm limits. Use actual fixed-argument evaluation bounds,
    bounded complex scalar maps and the existing closed
    equalizer theorem. No differential conclusion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexScalarRealBounded ComplexScalarSlotUP FamilyUpdate NormMetric NormDifferentialUP
  NormBoundedLinearTopology RealMetricBackground ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearEvaluationBound ContinuousEqualizerClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Closed.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variable hNX:is_complex_norm NX.
Variable hNY:is_complex_norm NY.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation hNYR:=(complex_norm_real hNY).
Variable k:nat.
Variable Z:lmodType R.
Variable ev:{ffun 'I_k->XR}->Hom Z YR.
Variable ZN:Z->R.
Variable hZ:@is_continuous_multilinear_space R k XR YR Z NX NY ev ZN.
Local Notation hZN:=(continuous_multilinear_norm_is_norm hNYR hZ).
Local Notation T:=(real_norm_metric_space hZN).
Local Notation TY:=(real_norm_metric_space hNYR).

(** Source for [complex_multilinear_slots_closed]: the
    original complex scalar equations form a closed subset
    of the actual real continuous-multilinear operator space,
    supporting the complex normal-series argument in 3.4.12,
    pp. 338–339. The empty family is included. *)
Theorem complex_multilinear_slots_closed:
  @closed T [set z:T|has_complex_scalar_slot_laws (fun u=>ev u z)].
Proof.
have hEvaluation (u:{ffun 'I_k->X}):continuous (fun z:T=>(ev u z:TY)).
  exact:(@norm_bounded_linear_continuous R Z YR ZN NY hZN hNYR (ev u)
    (@continuous_multilinear_evaluation_bounded R k XR YR Z NX NY hNXR ev ZN hZ u)).
have hScalar (c:ComplexScalars.C R):continuous (fun y:TY=>(c*:(y:Y):TY)).
  have [M [hValues hBound]]:=@complex_scalar_real_bounded_exists R Y NY hNY c.
  have hMap:=@norm_bounded_linear_continuous R YR YR NY NY hNYR hNYR M hBound.
  have hSame:(fun y:TY=>(c*:(y:Y):TY))=(fun y:TY=>(M y:TY)).
    apply:funext=>y;exact:esym (hValues y).
  by rewrite hSame.
have hSame:[set z:T|has_complex_scalar_slot_laws (fun u=>ev u z)]=
    \bigcap_(u in [set:{ffun 'I_k->X}]) \bigcap_(i in [set:'I_k])
    \bigcap_(c in [set:ComplexScalars.C R]) \bigcap_(x in [set:X])
      [set z:T|ev (@family_with k (fun _=>X) u i (c*:x)) z=
        c*:ev (@family_with k (fun _=>X) u i x) z].
  apply/seteqP;split=>z h.
  - move=>u _ i _ c _ x _;exact:h u i c x.
  - move=>u i c x;exact:h u Logic.I i Logic.I c Logic.I x Logic.I.
rewrite hSame;apply:closed_bigI=>u _;apply:closed_bigI=>i _;
  apply:closed_bigI=>c _;apply:closed_bigI=>x _.
apply:(@continuous_equalizer_closed T TY
  (fun z:T=>(ev (@family_with k (fun _=>X) u i (c*:x)) z:TY))
  (fun z:T=>(c*:(ev (@family_with k (fun _=>X) u i x) z:Y):TY)) (@metric_hausdorff R TY));
  first exact:hEvaluation.
move=>z;exact:continuous_comp
  (hEvaluation (@family_with k (fun _=>X) u i x) z)
  (hScalar c (ev (@family_with k (fun _=>X) u i x) z)).
Qed.

(** Source for [complex_multilinear_slots_limit]: original
    complex scalar equations survive an actual convergent
    operator sequence, 3.4.12, pp. 338–339.
    Apply the proved closed-set law to that sequence. *)
Theorem complex_multilinear_slots_limit (u:nat->Z) (z:Z):
  (forall N,has_complex_scalar_slot_laws (fun v=>ev v (u N))) ->
  ((fun N=>(u N:T)) @ \oo --> (z:T)) ->
  has_complex_scalar_slot_laws (fun v=>ev v z).
Proof.
move=>hEach hLimit.
have hEvent: \forall N \near \oo,has_complex_scalar_slot_laws (fun v=>ev v (u N)).
  exists 0%N=>//N hN;exact:hEach.
have PF:ProperFilter (\oo:set_system nat) by typeclasses eauto.
exact:(@closed_cvg nat T \oo PF u
  (fun w:T=>has_complex_scalar_slot_laws (fun v=>ev v w))
  complex_multilinear_slots_closed hEvent z hLimit).
Qed.
End Closed.
