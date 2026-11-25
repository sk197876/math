(** Federer (1969), 4.1.25, p. 383: public
    laws for the Lipschitz image of a compact
    summable source-top multivector field. The first
    action formula retains the full original partial
    differential, including critical points. The second
    identifies the actual sealed image with the
    actual Hausdorff-density current of the original
    full-fibre sum. Summability, its conull domain,
    the exact support image, associated tangent and
    signed Euclidean-norm formula are proved separately.
    The literal simplicity clause has positive degree;
    the actual zero-degree boundary calculation is
    exposed beside it. No private construction field
    is part of this interface. *)
From Federer Require Export
  CurrentLipschitzLebesgueAction
  CurrentAreaNormalisedImageLaws
  CurrentAreaFibreDensityDomain
  CurrentAreaFibreDensityMeasurable
  CurrentAreaFibreDensitySummable
  CurrentLipschitzHausdorffAction
  CurrentLipschitzHausdorffDensity
  CurrentLipschitzAreaGeometry
  CurrentAreaZeroDegreeSimplicity.
