(** Federer (1969), 4.1.18, p. 375: the
    translated compact scalar tests used to average
    the original variation are compact tests on the
    actual full current domain. The translation is
    globally proper regardless of the current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealMetricBackground RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain FiniteNormCompactHull
  SmoothCompactSet SmoothCompactTranslate EuclideanFullDomainCompactFunctions
  CompactSupportFunctionUP FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanTranslatedCompactFunctions.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation FT:=(current_domain R n Full).

(** Source for [euclidean_translated_compact_function]:
    translating an original compact scalar test
    preserves its continuity and compact support,
    supporting the literal measure average in
    Federer 4.1.18, p. 375. *)
Theorem euclidean_translated_compact_function (f:XT->R) z:
  compactly_supported_continuous_functions f ->
  compactly_supported_continuous_functions (fun x:XT=>f (x+z)).
Proof.
move=>hF;split.
- move=>x;apply:(@continuous_comp XT XT (real_line_metric R)
    (fun y:XT=>y+z) f x).
  + exact:(@norm_translation_continuous R X NX hNX z x).
  + exact:hF.1.
- pose K:=@Build_smooth_compact_set R X NX hNX Full
    (real_function_support f) (fun _ _=>Logic.I) hF.2.
  pose L:=@smooth_compact_translate R X NX hNX K z.
  have hL:@compact XT (smooth_compact_carrier L):=smooth_compact_is_compact L.
  have hClosed:@closed XT (smooth_compact_carrier L).
    exact:compact_closed (@metric_hausdorff R XT) hL.
  apply:(@real_function_compact_support_in_closed_set R XT
    (fun x:XT=>f (x+z)) (smooth_compact_carrier L) hL hClosed)=>x hx.
  apply:real_function_zero_off_support.
  exact:hx.
Qed.

(** Source for [euclidean_full_translated_positive_compact]:
    each translated positive test has its literal
    finite integral against the original full-domain
    Radon variation, supporting 4.1.18, p. 375. *)
Theorem euclidean_full_translated_positive_compact (f:XT->R) z:
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  positive_function_lattice (@compactly_supported_continuous_functions R FT)
    (fun x:FT=>f (set_val x+z)).
Proof.
move=>hF;split.
- exact:(@euclidean_full_compact_function_pullback R n
    (fun x:XT=>f (x+z)) (euclidean_translated_compact_function z hF.1)).
- by move=>x;exact:hF.2 (set_val x+z).
Qed.
End EuclideanTranslatedCompactFunctions.
