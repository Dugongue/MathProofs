import copy
import random
import json
from pathlib import Path
import unittest
from design_boolean.core import recognize, verify_certificate
from independent import (support_design, quadratic_truth, cubic_plateaued_truth,
                         sum_free_counterexample, check_certificate, walsh)


class RecognitionTests(unittest.TestCase):
    def assertRecognized(self, matrix):
        result = recognize(matrix)
        self.assertEqual(result.status, 'recognized', result.to_dict())
        self.assertTrue(result.certificate)
        valid, reason = check_certificate(matrix, result.certificate)
        self.assertTrue(valid, reason)
        audit = verify_certificate(matrix, result.certificate)
        self.assertTrue(audit.valid, audit.reason)
        return result

    def test_published_fixture_manifest(self):
        folder=Path(__file__).resolve().parents[1]/'examples'
        manifest=json.loads((folder/'manifest.json').read_text(encoding='utf-8'))
        for entry in manifest['fixtures']:
            with self.subTest(fixture=entry['file']):
                fixture=json.loads((folder/entry['file']).read_text(encoding='utf-8'))
                matrix=fixture['incidence']
                result=recognize(matrix)
                expected='recognized' if fixture['expected']['recognized'] else 'not_recognized'
                self.assertEqual(result.status,expected,result.to_dict())
                if expected=='recognized':
                    valid,reason=check_certificate(matrix,result.certificate)
                    self.assertTrue(valid,reason)

    def test_labels_retained(self):
        matrix=support_design(quadratic_truth(4))
        points=['point-'+str(i) for i in range(16)]
        blocks=['block-'+str(i) for i in range(16)]
        result=recognize(matrix,point_labels=points,block_labels=blocks)
        self.assertEqual(result.status,'recognized')
        self.assertEqual(result.certificate['point_labels'],points)
        self.assertEqual(result.certificate['block_labels'],blocks)

    def test_quadratic_bent(self):
        for m in (4, 6):
            with self.subTest(m=m):
                matrix = support_design(quadratic_truth(m))
                result = self.assertRecognized(matrix)
                self.assertEqual(result.certificate['amplitude'], 1 << (m // 2))

    def test_nonlinear_plateaued(self):
        for extra in (0, 1):
            with self.subTest(extra=extra):
                truth = cubic_plateaued_truth(extra)
                self.assertRecognized(support_design(truth))

    def test_permuted_labels(self):
        matrix = support_design(cubic_plateaued_truth())
        for seed in range(8):
            rng = random.Random(seed)
            points = list(range(len(matrix)))
            blocks = list(range(len(matrix[0])))
            rng.shuffle(points)
            rng.shuffle(blocks)
            shuffled = [[matrix[p][b] for b in blocks] for p in points]
            self.assertRecognized(shuffled)

    def test_bit_corruption_rejected(self):
        matrix = support_design(quadratic_truth(4))
        matrix[2][7] ^= 1
        self.assertNotEqual(recognize(matrix).status, 'recognized')

    def test_simple_design_negative_counterexample(self):
        matrix = sum_free_counterexample()
        self.assertEqual(len(matrix), 64)
        self.assertEqual(len(matrix[0]), 128)
        self.assertEqual({sum(row[b] for row in matrix) for b in range(128)}, {28})
        self.assertEqual({sum(a & b for a,b in zip(matrix[i], matrix[j]))
                          for i in range(64) for j in range(i)}, {24})
        result = recognize(matrix)
        self.assertEqual(result.status, 'not_recognized', result.to_dict())

    def test_repeated_columns_rejected(self):
        matrix = support_design(quadratic_truth(4))
        for row in matrix:
            row[-1] = row[0]
        self.assertNotEqual(recognize(matrix).status, 'recognized')

    def test_linear_structure_rejected(self):
        base = quadratic_truth(4)
        truth = base + base
        self.assertNotEqual(recognize(support_design(truth)).status, 'recognized')

    def test_unsupported_small_design(self):
        self.assertEqual(recognize(support_design(quadratic_truth(2))).status, 'unsupported')

    def test_malformed_input(self):
        for matrix in ([], [[]], [[0, 1], [1]], [[0, 2]], [[0, '1']]):
            with self.subTest(matrix=matrix):
                self.assertEqual(recognize(matrix).status, 'invalid_input')

    def test_certificate_tampering(self):
        matrix = support_design(cubic_plateaued_truth())
        result = self.assertRecognized(matrix)
        fields = ['truth_table', 'block_coordinates', 'point_frequencies', 'point_offsets']
        for field in fields:
            cert = copy.deepcopy(result.certificate)
            cert[field][0] ^= 1
            independent_valid, _ = check_certificate(matrix, cert)
            self.assertFalse(independent_valid, field)
            self.assertFalse(verify_certificate(matrix, cert).valid, field)
        cert = copy.deepcopy(result.certificate)
        cert['amplitude'] += 1
        self.assertFalse(verify_certificate(matrix, cert).valid)

    def test_boolean_function_spectrum_independent(self):
        truth = cubic_plateaued_truth()
        spectrum = walsh(truth)
        self.assertEqual(set(spectrum), {-8, 0, 8})
        for a in range(1, len(truth)):
            self.assertGreater(len({truth[x ^ a] ^ truth[x] for x in range(len(truth))}), 1)


if __name__ == '__main__':
    unittest.main()
