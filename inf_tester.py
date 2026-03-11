import unittest
from types import SimpleNamespace
import re

from inf import Inference


class FakePrime:
	def __init__(self, literals_list):
		self.literals_list = literals_list


class FakeOrbit:
	def __init__(self, repr_literals, prime_literals_list):
		self.repr_prime = FakePrime(repr_literals)
		self.primes = [FakePrime(lits) for lits in prime_literals_list]


class InferenceEnumerateTests(unittest.TestCase):
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
		)

	def _make_inf(self, repr_literals, primes):
		orbit = FakeOrbit(repr_literals, primes)
		options = SimpleNamespace()
		protocol = self._build_fake_protocol(repr_literals, primes)
		return Inference(orbit=orbit, options=options, protocol=protocol, is_dnf=False)

	def test_empty_clause(self):
		inf = self._make_inf([], [[]])
		out = inf.get_qclause()
		print("empty clause final value")
		print(out)


	def test_single_literal_two_args(self):
		repr_lits = ['e(node0,node1)']
		primes = [
			['e(node0,node1)'],
			['e(node1,node0)'],
		]
		inf = self._make_inf(repr_lits, primes)
		out = inf.get_qclause()

		print("2 arg clause final value")
		print(out)

	def test_multiple_literals_with_negation(self):
		repr_lits = ['e(node0)', 'h(node1)', '~l(node1)']
		primes = [
			['e(node0)', 'h(node1)', '~l(node1)'],
			['e(node1)', 'h(node0)', '~l(node0)'],
		]
		inf = self._make_inf(repr_lits, primes)
		out = inf.get_qclause()

		print("multi literal clause final value")
		print(out)


if __name__ == '__main__':
	unittest.main(verbosity=2)
