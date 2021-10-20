import sage.algebras.commutative_dga
from sage.all import *


class Cohomology:
    @staticmethod
    def check_generator_names(generators):
        for (i, x) in enumerate(generators):
            if "," in x or " " in x or "G" in x:
                raise ValueError(f"Generators should not contain ',', 'G' or ' ': {x}")
            for y in generators[:i]:
                if x in y or y in x:
                    raise ValueError(
                        f"Generators should not be substrings of each other: {x}, {y}"
                    )

    def __init__(self, dimension, generators_with_grades, relations=None, diagonal="0"):
        if type(generators_with_grades) != type({}):
            self.generators_with_grades = {x: 1 for x in generators_with_grades}
        else:
            self.generators_with_grades = generators_with_grades
        self.dimension = dimension
        self.generators = list(self.generators_with_grades.keys())
        Cohomology.check_generator_names(self.generators)
        self.relations_as_strings = relations if relations is not None else []
        self.diagonal = diagonal


class TotaroAlgebra:
    @staticmethod
    def tuple_to_string(name, *indices):
        parts = [name] + [str(i) for i in indices]
        return "".join(parts)

    @staticmethod
    def trace_on_span(basis, permutation):
        if not basis:
            return 0
        dimension = len(basis[0])
        V = QQ ^ dimension
        permutation = V.hom(permutation, V)
        restriction = permutation.restrict(V.subspace_with_basis(basis))
        return restriction.trace()

    def pretty_print_cohomology(self, dictionary):
        ps, qs = set(), set()
        for p, q in dictionary:
            ps.add(p)
            qs.add(q)
        p_min = min(ps)
        p_max = max(ps)
        q_min = min(qs)
        q_max = max(qs)
        entries = [
            ["" for _ in range(p_min, p_max + 2)] for _ in range(q_min, q_max + 2)
        ]
        for q in range(q_max, q_min - 1, -1):
            entries[q_max - q][0] = str(q)
        for p in range(p_min, p_max + 1):
            entries[q_max - q_min + 1][p - p_min + 1] = str(p)
        for (p, q), d in dictionary.items():
            entries[q_max - q][p - p_min + 1] = str(d)
        column_widths = [0 for _ in range(p_min, p_max + 2)]
        for row in entries:
            for (i, s) in enumerate(row):
                column_widths[i] = max(column_widths[i], len(s))
        for row in entries:
            for i in range(len(row)):
                l = len(row[i])
                row[i] = " " * (column_widths[i] - l) + row[i]
        for row in entries:
            print(" | ".join(row))
        bad_example = None
        for p, q in dictionary:
            if bad_example is not None:
                break
            for p2, q2 in dictionary:
                if p + q + 1 == p2 + q2 and p + self.dimension <= p2:
                    bad_example = ((p, q), (p2, q2))
                    break
        if bad_example is not None:
            print(f"There might be higher differentials: {bad_example}")

    def __init__(self, cohomology, points=2):
        self.base_cohomology = cohomology
        self.dimension = cohomology.dimension
        self.points = points
        self.index_pairs = [(i, j) for i in range(points) for j in range(i + 1, points)]
        self.set_max_degrees()
        self.cohomology_computed = False
        self.cohomology_dimensions_computed = False
        self.cohomology_degrees = {}

        self.generators_with_grades = [
            (
                TotaroAlgebra.tuple_to_string(x, i),
                (cohomology.generators_with_grades[x], 0),
            )
            for x in cohomology.generators
            for i in range(points)
        ]
        for i, j in self.index_pairs:
            self.generators_with_grades.append(
                (TotaroAlgebra.tuple_to_string("G", i, j), (0, self.dimension - 1))
            )

        # print self.generators_with_grades
        A = sage.algebras.commutative_dga.GradedCommutativeAlgebra(
            QQ,
            ",".join((x for x, _ in self.generators_with_grades)),
            tuple(d for _, d in self.generators_with_grades),
        )

        self.process_generators(A.gens())
        # A.inject_variables()

        self.process_relations()

        I = A.ideal(self.relations_symbolic)
        self.algebra = A.quotient(I)

        self.process_pq_terms()

        differential_dict_strings = {
            f"G{i}{j}": cohomology.diagonal.format(i=i, j=j)
            for i, j in self.index_pairs
        }
        differential_dict_symbolic = {
            self.string_to_symbolic(g): self.string_to_symbolic(dg)
            for g, dg in differential_dict_strings.items()
        }

        print(differential_dict_symbolic)
        # TODO: deal with zero differential

        self.algebra = self.algebra.cdg_algebra(differential_dict_symbolic)

        self.process_group()

    def process_generators(self, generators_symbolic):
        self.generators_string_to_symbolic = {
            x: generators_symbolic[i]
            for i, (x, _) in enumerate(self.generators_with_grades)
        }

        self.generators_tuple_to_symbolic = {
            (x, (i,)): self.generators_string_to_symbolic[
                TotaroAlgebra.tuple_to_string(x, i)
            ]
            for x in self.base_cohomology.generators
            for i in range(self.points)
        }
        for i, j in self.index_pairs:
            self.generators_tuple_to_symbolic[
                ("G", (i, j))
            ] = self.generators_string_to_symbolic[
                TotaroAlgebra.tuple_to_string("G", i, j)
            ]

        self.generators_symbolic_to_tuple = {
            a: b for b, a in self.generators_tuple_to_symbolic.items()
        }
        self.generators_tuple = [
            self.generators_symbolic_to_tuple[x] for x in generators_symbolic
        ]
        # print generators_tuple_to_symbolic

    def generator_from_string(self, string):
        return self.generators_string_to_symbolic[string]

    def string_to_symbolic(self, string):
        return sage_eval(string, locals=self.generators_string_to_symbolic)

    def process_relations(self):
        self.relations_string = [f"G{i}{j}^2" for i, j in self.index_pairs]
        self.relations_string.extend(
            [
                f"G{i}{j}*G{j}{k} + G{j}{k}*G{i}{k} + G{i}{k}*G{i}{j}"
                for (i, j) in self.index_pairs
                for (j2, k) in self.index_pairs
                if j == j2
            ]
        )
        # self.relations_string.extend(
        #    [f"G{i}{j} - (-1)^{self.dimension}*(G{j}{i})" for i, j in self.index_pairs]
        # )
        for rel in self.base_cohomology.relations_as_strings:
            for gen in self.base_cohomology.generators:
                rel = rel.replace(gen, gen + "{index}")
            for i in range(self.points):
                self.relations_string.append(rel.format(index=i))
        for gen in self.base_cohomology.generators:
            for i, j in self.index_pairs:
                self.relations_string.append(
                    f"{gen}{i}*G{i}{j} - {gen}{j}*G{i}{j}"
                )  # edit for odd dimensions, if ever

        self.relations_symbolic = [
            self.string_to_symbolic(rel) for rel in self.relations_string
        ]

    def set_max_degrees(self):
        self.p_max = (self.dimension) * (self.points)
        self.q_max = (self.dimension - 1) * len(self.index_pairs) // 2

    def process_pq_terms(self):
        # self.p_terms = [p for p in range(0, self.p_max+1) if self.algebra.basis((p, 0))]
        q_terms = [
            q
            for q in range(0, self.q_max + 1, self.dimension - 1)
            if self.algebra.basis((0, q))
        ]
        self.q_max = q_terms[-1]
        self.pq_terms = set()
        for p in range(self.p_max + 1):
            for q in q_terms:
                term = self.algebra.basis((p, q))
                if term:
                    self.pq_terms.add((p, q))
                else:
                    break
        # print(self.pq_terms)

    def print_cohomology(self, irrep=None):
        if not self.cohomology_computed:
            self.find_cohomology_as_representations()

        dictionary = {}
        for degree, character in self.cohomology_degrees.items():
            multiplicity = self.multiplicity(character, irrep)
            if multiplicity:
                dictionary[degree] = multiplicity
        self.pretty_print_cohomology(dictionary)

    def print_E2(self, irrep=None):
        dictionary = {}
        E2 = {
            (p, q): len(self.algebra.basis((p, q)))
            for p in range(self.p_max)
            for q in range(self.q_max)
        }
        print(E2)

    def print_cohomology_dimensions(self):
        if self.cohomology_computed:
            self.pretty_print_cohomology(
                {
                    degree: character[0]
                    for degree, character in self.cohomology_degrees.items()
                }
            )
        if not self.cohomology_dimensions_computed:
            self.find_cohomology_dimensions()
        self.pretty_print_cohomology(self.cohomology_degrees)

    def find_cohomology_dimensions(self):
        for p, q in self.pq_terms:
            z = self.algebra.cocycles((p, q)).basis()
            b = self.algebra.coboundaries((p, q)).basis()
            self.cohomology_degrees[(p, q)] = z - b
        self.cohomology_dimensions_computed = True

    def multiplicity(self, character, irrep=None):
        if irrep is None:
            return character
        irrep_decomposition = self.decompose_character(irrep)
        if len(irrep_decomposition) != 1:
            raise ValueError(f"{irrep} is not irreducible")
        irrep = irrep_decomposition[0][1]
        for coefficient, irrep2 in self.decompose_character(character):
            if irrep2 == irrep:
                return coefficient

    def find_cohomology_in_degree(self, degree, irrep=None):
        if degree in self.cohomology_degrees and isinstance(
            self.cohomology_degrees[degree], list
        ):
            character = self.cohomology_degrees[degree]
        else:
            z = self.algebra.cocycles(degree).basis()
            b = self.algebra.coboundaries(degree).basis()
            if len(z) == len(b):
                return
            character = []
            for g in self.conjugacy_class_representatives:
                matrix = self.act_on_basis(degree, g)
                character.append(
                    TotaroAlgebra.trace_on_span(z, matrix)
                    - TotaroAlgebra.trace_on_span(b, matrix)
                )
        return self.multiplicity(character, irrep)

    def find_cohomology_as_representations(self):
        if self.cohomology_dimensions_computed:
            degrees = list(self.cohomology_degrees.keys())
            for degree in degrees:
                self.cohomology_degrees[degree] = self.find_cohomology_in_degree(degree)
        else:
            for degree in self.pq_terms:
                h = self.find_cohomology_in_degree(degree)
                if h:
                    self.cohomology_degrees[degree] = h
        self.cohomology_dimensions_computed = True
        self.cohomology_computed = True

    def act_on_generators(self, permutation):
        ret = []
        for x, subscripts in self.generators_tuple:
            new_subscripts = tuple(sorted(permutation(i + 1) - 1 for i in subscripts))
            ret.append(self.generators_tuple.index((x, new_subscripts)))
        return ret

    def act_on_element(self, vector, basis_map):
        new_terms = []
        for exponents, coefficient in vector.dict().items():
            # print(exponents, coefficient)
            new_term = self.algebra(coefficient)
            for i in range(len(exponents)):
                new_term *= (self.algebra.gens()[basis_map[i]]) ^ (exponents[i])
            new_terms.append(new_term)
        # print(vector, new_terms)
        image_vector = sum(new_terms)
        return image_vector

    def act_on_basis(self, degree, basis_map):
        basis = self.algebra.basis(degree)
        if not basis:
            return []
        dimension = len(basis)
        matrix = [[0 for _ in range(dimension)] for _ in range(dimension)]
        for j, vector in enumerate(basis):
            image_vector = self.act_on_element(vector, basis_map)
            # print(vector, image_vector)
            for i, aij in enumerate(image_vector.basis_coefficients()):
                matrix[j][i] = aij  # matrix is list of columns
        # print(matrix)
        return matrix

    def process_group(self):
        self.sn = SymmetricGroup(self.points)
        self.conjugacy_class_representatives = [
            self.act_on_generators(c.representative())
            for c in self.sn.conjugacy_classes()
        ]
        # print(self.algebra.gens())
        # print(self.conjugacy_class_representatives)

    def decompose_character(self, character):
        return self.sn.character(character).decompose()


def complex_projective_space(dimension):
    diagonal = " + ".join(
        f"x{{i}}^{p}*x{{j}}^{dimension - p}" for p in range(dimension + 1)
    )
    return Cohomology(2 * dimension, {"x": 2}, [f"x^({dimension}+1)"], diagonal)


P1 = complex_projective_space(1)
P2 = complex_projective_space(2)
# P2 = Cohomology(4, {'x':2}, ['x^3'], 'x{i}^2 + x{i}*x{j} + x{j}^2')

H = TotaroAlgebra(complex_projective_space(4), 3)
# H.print_E2()
H.print_cohomology([1, -1, 1])
# for character in H.sn:
#     print(character)
#     H.print_cohomology(character)
# H.print_cohomology([1, 1, 1])

# X = Cohomology(6, {'x':2}, ['x^3'], 'x{i}^2*x{j} + x{i}*x{j}^2')
# H = TotaroAlgebra(X,3)
# H.print_cohomology()

# C4 = Cohomology(8, {})
# TotaroAlgebra(C4, 3).print_cohomology()
