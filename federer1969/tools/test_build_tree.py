"""Run with python3 -B -m unittest discover -s tools -p 'test_build_tree.py'."""
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_tree


class BuildTreeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'source'
        self.build = Path(self.temp.name) / 'build'
        (self.root / 'theories').mkdir(parents=True)
        (self.root / 'tests').mkdir()
        (self.root / '_CoqProject').write_text('-Q theories Federer\ntheories/Example.v\n')
        (self.root / 'theories/Example.v').write_text('Lemma example : True. Proof. exact I. Qed.\n')
        patcher = patch.object(build_tree, 'ROOT', self.root)
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_prepare_is_repeatable_and_preserves_source(self):
        build_tree.prepare(self.build)
        build_tree.prepare(self.build)
        link = self.build / 'theories/Example.v'
        self.assertTrue(link.is_symlink())
        self.assertEqual(link.resolve(), self.root / 'theories/Example.v')

    def test_refuse_another_checkout(self):
        build_tree.prepare(self.build)
        with patch.object(build_tree, 'ROOT', Path(self.temp.name) / 'different'):
            with self.assertRaises(ValueError):
                build_tree.prepare(self.build)

    def test_refuse_nonempty_unmarked_directory(self):
        self.build.mkdir()
        (self.build / 'unrelated').write_text('preserve me')
        with self.assertRaises(ValueError):
            build_tree.prepare(self.build)
        self.assertEqual((self.build / 'unrelated').read_text(), 'preserve me')

    def test_removed_source_cannot_leave_importable_artifact(self):
        build_tree.prepare(self.build)
        for artifact in build_tree.artifact_paths(self.build / 'theories/Example.v'):
            artifact.write_bytes(b'old artifact')
        (self.root / 'theories/Example.v').unlink()
        build_tree.prepare(self.build)
        self.assertEqual(list((self.build / 'theories').iterdir()), [])

    def test_migration_preserves_bytes_and_age_and_archives_obsolete_files(self):
        source = self.root / 'theories/Example.vo'
        source.write_bytes(b'cached artifact')
        os.utime(source, ns=(1_000_000_000, 2_000_000_000))
        (self.root / 'theories/Removed.vo').write_bytes(b'obsolete')
        (self.root / 'Makefile.coq').write_text('old absolute paths')
        build_tree.migrate(self.build)
        target = self.build / 'theories/Example.vo'
        self.assertEqual(target.read_bytes(), b'cached artifact')
        self.assertEqual(target.stat().st_mtime_ns, 2_000_000_000)
        self.assertFalse(source.exists())
        self.assertTrue((self.root / 'theories/Example.v').is_file())
        self.assertTrue((self.build / 'previous-build/theories/Removed.vo').is_file())
        self.assertTrue((self.build / 'previous-build/Makefile.coq').is_file())
        self.assertFalse((self.build / 'theories/Removed.vo').exists())

    def test_collision_preserves_original(self):
        build_tree.prepare(self.build)
        original = self.root / 'theories/Example.vo'
        original.write_bytes(b'original')
        (self.build / 'theories/Example.vo').write_bytes(b'existing')
        with self.assertRaises(ValueError):
            build_tree.migrate(self.build)
        self.assertEqual(original.read_bytes(), b'original')

    def test_reject_source_and_parent_as_destination(self):
        for path in (self.root, self.root.parent, self.root / 'theories'):
            with self.assertRaises(ValueError):
                build_tree.build_directory(str(path))


if __name__ == '__main__':
    unittest.main()
