import unittest
from types import SimpleNamespace
import re

from inf import Inference
from ivy import ivy_logic as il


class FakePrime:
	def __init__(self, literals_list):
		self.literals_list = literals_list
	def __str__(self) -> str:
		s = ""
		for i in self.literals_list:
			s += i + ", "
		return s

class FakeOrbit:
	def __init__(self, repr_literals, prime_literals_list):
		self.repr_prime = FakePrime(repr_literals)
		all_primes = [FakePrime(lits) for lits in prime_literals_list]
		self.primes = all_primes
		self.suborbit_repr_primes = all_primes
		self.suborbitrepr_primes = all_primes


class InferenceEnumerateTests(unittest.TestCase):
	def _collect_var_nodes(self, term):
		vars_found = []

		def walk(node):
			if type(node).__name__ == 'Var':
				vars_found.append(node)
			for arg in getattr(node, 'args', []):
				walk(arg)

		walk(term)
		return vars_found

	def _build_fake_protocol(self, repr_literals, primes):
		all_literals = list(repr_literals)
		for p in primes:
			all_literals.extend(p)

		consts = set()
		predicates = {}

		for lit in all_literals:
			token = lit.strip()
			if token.startswith('~'):
				token = token[1:].strip()

			m_rel = re.match(r'^([\w.]+)\(([^)]*)\)$', token)
			if m_rel:
				pred = m_rel.group(1)
				args = [arg.strip() for arg in m_rel.group(2).split(',') if arg.strip()]
				predicates[pred] = tuple(['node'] * len(args))
				for a in args:
					consts.add(a)
				continue

			if token.startswith('(') and token.endswith(')') and '=' in token:
				inner = token[1:-1].strip()
				m_fun_eq = re.match(r'^([\w.]+)\(([^)]*)\)=([\w.]+)$', inner)
				if m_fun_eq:
					pred = m_fun_eq.group(1) + '='
					lhs_args = [arg.strip() for arg in m_fun_eq.group(2).split(',') if arg.strip()]
					rhs = m_fun_eq.group(3).strip()
					args = lhs_args + [rhs]
					predicates[pred] = tuple(['node'] * len(args))
					for a in args:
						consts.add(a)
					continue

				m_eq = re.match(r'^([\w.]+)=([\w.]+)$', inner)
				if m_eq:
					pred = m_eq.group(1) + '='
					args = [m_eq.group(2).strip()]
					predicates[pred] = tuple(['node'] * len(args))
					for a in args:
						consts.add(a)

		if not consts:
			consts = {'node0', 'node1'}

		return SimpleNamespace(
			sorts=['node'],
			sort_constants=[sorted(consts)],
			predicates=predicates,
			get_sort_quantifier_name=lambda sort_name, idx: f'{str(sort_name).upper()}{idx}',
		)

	def _make_inf(self, repr_literals, primes):
		orbit = FakeOrbit(repr_literals, primes)
		options = SimpleNamespace()
		protocol = self._build_fake_protocol(repr_literals, primes)
		return Inference(orbit=orbit, options=options, protocol=protocol, is_dnf=False)

	def test_empty_clause(self):
		inf = self._make_inf([], [[]])
		out = inf.get_qclause()
		print("\nempty clause final value")
		print(out)


	def test_single_literal_two_args(self):
		repr_lits = ['e(node0,node1)']
		primes = [
			['e(node0,node1)'],
			['e(node1,node0)'],
		]
		inf = self._make_inf(repr_lits, primes)
		out = inf.get_qclause()

		print("\n2 arg clause final value")
		print(out)

	def test_multiple_literals_with_negation(self):
		repr_lits = ['e(node0)', 'h(node1)', '~l(node1)']
		primes = [
			['e(node0)', 'h(node1)', '~l(node1)'],
			['e(node1)', 'h(node0)', '~l(node0)'],
		]
		inf = self._make_inf(repr_lits, primes)
		out = inf.get_qclause()

		print("\nmulti literal clause final value")
		print(out)

	def test_no_cross_sort_equality_vars(self):
		repr_lits = ['mix(node0,epoch0)']
		primes = [
			['mix(node0,epoch0)'],
		]
		orbit = FakeOrbit(repr_lits, primes)
		options = SimpleNamespace()
		protocol = SimpleNamespace(
			sorts=['node', 'epoch'],
			sort_constants=[['node0', 'node1'], ['epoch0', 'epoch1']],
			predicates={'mix': ('node', 'epoch')},
			get_sort_quantifier_name=lambda sort_name, idx: f'{str(sort_name).upper()}{idx}',
		)
		inf = Inference(orbit=orbit, options=options, protocol=protocol, is_dnf=False)
		out = inf.get_qclause()

		self.assertNotRegex(str(out['restrictions']), r'e\d+\d+')
		print("\nmixed sort clause final value")
		print(out)

	def test_multiple_suborbit_representatives(self):
		repr_lits = ['e(node0,node1)']
		primes = [
			['e(node0,node1)'],
			['e(node0,node0)'],
			['e(node1,node0)'],
		]
		orbit = FakeOrbit(repr_lits, primes)
		orbit.suborbit_repr_primes = [orbit.primes[0], orbit.primes[1]]
		orbit.suborbitrepr_primes = orbit.suborbit_repr_primes

		options = SimpleNamespace()
		protocol = self._build_fake_protocol(repr_lits, primes)
		inf = Inference(orbit=orbit, options=options, protocol=protocol, is_dnf=False)
		out = inf.get_qclause()

		self.assertRegex(str(out['qclause']), r'(~e\(NODE0,NODE1\)|\(true\s*->)')
		self.assertNotRegex(str(out['restrictions']), r'e\d+\d+')
		print("\nmultiple suborbit representatives final value")
		print(out)

	def test_forced_equality_merges_quantifiers(self):
		repr_lits = ['e(node0,node0)']
		primes = [
			['e(node0,node0)'],
			['e(node1,node1)'],
		]
		inf = self._make_inf(repr_lits, primes)
		out = inf.get_qclause()

		self.assertRegex(str(out['qclause']), r'^forall NODE0')
		self.assertNotIn('NODE1', str(out['qclause']))
		print("\nforced equality merges quantifiers final value")
		print(out)

	def test_forced_equality_reuses_quantified_var_object(self):
		repr_lits = ['e(node0,node0)']
		primes = [
			['e(node0,node0)'],
			['e(node1,node1)'],
		]
		inf = self._make_inf(repr_lits, primes)
		out = inf.get_qclause()

		qclause = out['qclause']
		self.assertIsInstance(qclause, il.ForAll)
		qvars = list(il.quantifier_vars(qclause))
		self.assertEqual(len(qvars), 1)
		qvar = qvars[0]

		body = il.quantifier_body(qclause)
		body_vars = self._collect_var_nodes(body)
		self.assertGreaterEqual(len(body_vars), 2)
		self.assertTrue(all(v is qvar for v in body_vars))



if __name__ == '__main__':
	unittest.main(verbosity=2)
