"""Focused audit import boundaries must preserve exact qualified identities."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from dependency_audit import qualified_query_import


class QualifiedAuditImportTests(unittest.TestCase):
    def test_nested_sealed_constant_keeps_its_actual_source_module(self):
        self.assertEqual(qualified_query_import(
            'Federer.InjectionExtensionSealed.InjectionExtension.value',
            {'theories/InjectionExtensionSealed'}),
            'From Federer Require Import InjectionExtensionSealed.')

    def test_test_namespace_is_not_confused_with_theory_namespace(self):
        self.assertEqual(qualified_query_import(
            'FedererTests.StructureTrichotomyExamples.structure_trichotomy_positive_zero_atom',
            {'tests/StructureTrichotomyExamples'}),
            'From FedererTests Require Import StructureTrichotomyExamples.')
        with self.assertRaises(ValueError):
            qualified_query_import('FedererTests.Examples.example', {'theories/Examples'})

    def test_unqualified_unresolved_and_ambiguous_queries_fail_closed(self):
        cases = [
            ('tensor_unique', {'theories/TensorUP'}),
            ('Federer.TensorUP.tensor_unique', None),
            ('Federer.TensorUP.tensor_unique', {'theories/Other'}),
            ('Federer.TensorUP.tensor_unique', {'theories/TensorUP', 'tests/TensorUP'}),
        ]
        for name, modules in cases:
            with self.subTest(name=name, modules=modules), self.assertRaises(ValueError):
                qualified_query_import(name, modules)


if __name__ == '__main__':
    unittest.main()
