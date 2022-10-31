import itertools
from collections import defaultdict
from collections.abc import Callable, Iterable
from functools import cached_property
from typing import Any, overload

import sage.algebras.commutative_dga
import sage.groups.perm_gps.permgroup_named


def tuple_to_string(gen: tuple[str, tuple[int, ...]]) -> str:
    name, indices = gen
    return name + name.join(str(x) for x in indices)


def print_ss(terms: dict[tuple[int, int], Any], page_index: int = 2) -> None:
    print_ss_page(terms)
    differentials = defaultdict(list)
    for (p1, q1), (p2, q2) in itertools.combinations(terms, 2):
        if (r := p2 - p1) == q1 - q2 + 1 >= page_index:
            differentials[r].append(((p1, q1), (p2, q2)))
    if differentials:
        print("There may be non-zero differentials:")
        # TODO check characters
        for r, arrows in sorted(differentials.items()):
            arrows_string = ", ".join(f"{s} -> {t}" for s, t in arrows)
            print(f"\ton page {r}: {arrows_string}")


def print_ss_page(terms: dict[tuple[int, int], Any]) -> None:
    ps, qs = set(), set()
    for p, q in terms:
        ps.add(p)
        qs.add(q)
    p_min = min(0, min(ps))
    p_max = max(ps)
    q_min = min(0, min(qs))
    q_max = max(qs)
    row_list = [["" for _ in range(p_min, p_max + 2)] for _ in range(q_min, q_max + 2)]
    for q in range(q_min, q_max + 1):
        row_list[q - q_min + 1][0] = str(q)
    row_list[0][1:] = (str(p) for p in range(p_min, p_max + 1))
    for (p, q), d in terms.items():
        row_list[q - q_min + 1][p - p_min + 1] = str(d)
    column_widths = [max(len(s) for s in column) for column in zip(*row_list)]
    for row in reversed(row_list[1:]):
        print_row(column_widths, row)
    print(
        "-" * (column_widths[0] + 1)
        + "+"
        + "-" * (sum(column_widths[1:]) + len(column_widths) - 1)
    )
    print_row(column_widths, row_list[0])


def print_row(column_widths: list[int], row: list[str]) -> None:
    strings = [f"{entry: >{width}}" for entry, width in zip(row, column_widths)]
    row_body = " ".join(strings[1:])
    print(f"{strings[0]} | {row_body}")


def trace_on_span(basis: list[list[int]], permutation: list[list[int]]) -> int:
    if not basis:
        return 0
    dimension = len(basis[0])
    V = QQ ^ dimension
    hom = V.hom(permutation, V)
    return hom.restrict(V.subspace_with_basis(basis)).trace()


class Cohomology:
    @staticmethod
    def check_generator_names(generators: Iterable[str]) -> None:
        for x in generators:
            if "," in x or " " in x or "G" in x:
                raise ValueError(f"Generators should not contain ',', 'G' or ' ': {x}")
        for x, y in itertools.combinations(generators, 2):
            if x in y or y in x:
                raise ValueError(
                    f"Generators should not be substrings of each other: {x}, {y}"
                )

    def __init__(
        self,
        dimension: int,
        generators: dict[str, int] | list[str],
        relations: list[str] | None = None,
        diagonal: str = "0",
    ) -> None:
        self.generators = (
            generators if isinstance(generators, dict) else {x: 1 for x in generators}
        )
        Cohomology.check_generator_names(self.generators.keys())
        self.dimension = dimension
        self.relations = relations if relations is not None else []
        self.diagonal = diagonal

    def totaro_generators(
        self, points: int
    ) -> list[tuple[tuple[str, tuple[int, ...]], tuple[int, int]]]:
        ret = [
            ((x, (i,)), (d, 0))
            for x, d in self.generators.items()
            for i in range(points)
        ] + [
            (("G", (i, j)), (0, self.dimension - 1))
            for i, j in itertools.combinations(range(points), 2)
        ]
        return sorted(ret, key=lambda x: sum(x[1]))


class TrivialModule:
    def __init__(self, rank: int) -> None:
        self.rank = rank

    @cached_property
    def _basis(self) -> list[list[int]]:
        return [
            [1 if i == j else 0 for j in range(self.rank)] for i in range(self.rank)
        ]

    def basis(self) -> list[list[int]]:
        return self._basis

    def dimension(self) -> int:
        return self.rank


class TrivialCDGA:
    def __init__(self, algebra) -> None:
        self.algebra = algebra

    def __call__(self, *args, **kwargs) -> Any:
        return self.algebra(*args, **kwargs)

    def gens(self) -> list:
        return self.algebra.gens()

    def basis(self, degree: tuple[int, int]) -> Any:
        return self.algebra.basis(degree)

    def cocycles(self, degree: tuple[int, int]) -> TrivialModule:
        return TrivialModule(len(self.algebra.basis(degree)))

    def coboundaries(self, degree: tuple[int, int]) -> TrivialModule:
        return TrivialModule(0)

    def cohomology(self, degree: tuple[int, int]) -> TrivialModule:
        return self.cocycles(degree)


class TotaroAlgebra:
    def __init__(self, cohomology: Cohomology, points: int = 2) -> None:
        self.base_cohomology = cohomology
        self.dimension = cohomology.dimension
        self.points = points
        self.cohomology_dimensions_computed = False
        self.cohomology_computed = False

        self.algebra, self.generator_string_to_symbolic = self.e2_algebra()
        self.algebra = self.cdga()

        self.sn, self.class_representatives = self.get_group_data()

    def e2_algebra(self):
        sorted_generators = sorted(
            [
                (tuple_to_string(gen), degree)
                for gen, degree in self.generator_dict.items()
            ],
            key=(lambda x: sum(x[1])),
        )
        # print(sorted_generators)
        A = sage.algebras.commutative_dga.GradedCommutativeAlgebra(
            QQ,
            names=[gen for gen, _ in sorted_generators],
            degrees=[degree for _, degree in sorted_generators],
        )

        string_to_symbolic = {
            gen_string: gen_symbolic
            for (gen_string, _), gen_symbolic in zip(sorted_generators, A.gens())
        }

        relations_string = [f"G{i}G{j}^2" for i, j in self.index_pairs] + [
            f"G{i}G{j}*G{j}G{k} + G{j}G{k}*G{i}G{k} + G{i}G{k}*G{i}G{j}"
            for (i, j, k) in itertools.combinations(range(self.points), 3)
        ]
        for rel in self.base_cohomology.relations:
            for generator in self.base_cohomology.generators:
                rel = rel.replace(generator, generator + "{index}")
            for i in range(self.points):
                relations_string.append(rel.format(index=i))
        for generator in self.base_cohomology.generators:
            for i, j in self.index_pairs:
                relations_string.append(
                    f"{generator}{i}*G{i}G{j} - {generator}{j}*G{i}G{j}"
                )  # edit for odd dimensions, if ever
        relations_symbolic = [
            sage_eval(rel, locals=string_to_symbolic) for rel in relations_string
        ]

        ideal = A.ideal(relations_symbolic)
        algebra = A.quotient(ideal)
        return algebra, string_to_symbolic

    def cdga(self):
        differential_dict_symbolic = self.differential

        if all(dg == 0 for dg in differential_dict_symbolic.values()):
            return TrivialCDGA(self.algebra)

        return self.algebra.cdg_algebra(differential_dict_symbolic)

    def get_group_data(self):
        sn = sage.groups.perm_gps.permgroup_named.SymmetricGroup(self.points)
        class_representatives = [
            self.act_on_generators(c.representative()) for c in sn.conjugacy_classes()
        ]
        return sn, class_representatives

    @cached_property
    def generator_dict(self):
        return dict(self.base_cohomology.totaro_generators(self.points))

    @cached_property
    def generator_list(self):
        return list(self.generator_dict.keys())

    @cached_property
    def differential(self) -> dict[Any, Any]:
        differential_dict_strings = {
            f"G{i}G{j}": self.base_cohomology.diagonal.format(i=i, j=j)
            for i, j in self.index_pairs
        }
        return {
            self.string_to_symbolic(g): self.string_to_symbolic(dg)
            for g, dg in differential_dict_strings.items()
        }

    @cached_property
    def e2_page(self) -> dict[tuple[int, int], int]:
        ret = {}
        for p in range(self.dimension * self.points + 1):
            for q in range(
                0, len(self.index_pairs) * (self.dimension - 1) + 1, self.dimension - 1
            ):
                basis = self.algebra.basis((p, q))
                if basis:
                    ret[(p, q)] = len(basis)
                else:
                    break
        return ret

    @cached_property
    def p_max(self) -> int:
        return max(p for p, _ in self.e2_page)

    @cached_property
    def q_max(self) -> int:
        return max(q for _, q in self.e2_page)

    @cached_property
    def index_pairs(self) -> list[tuple[int, int]]:
        return list(itertools.combinations(range(self.points), 2))

    def string_to_symbolic(self, string: str) -> Any:
        return sage_eval(string, locals=self.generator_string_to_symbolic)

    def print_E2(self, irrep: list[int] | None = None) -> None:
        print_ss(self.e2_page)

    def print_cohomology(self, irrep: list[int] | None = None) -> None:
        terms: dict[tuple[int, int], int | list[int]] = {}
        for degree, character in self.cohomology.items():
            multiplicity = self.multiplicity(character, irrep)
            if multiplicity:
                terms[degree] = multiplicity
        print_ss(terms, self.dimension + 1)

    def print_cohomology_dimensions(self) -> None:
        print_ss(self.cohomology_dimension, self.dimension + 1)

    @cached_property
    def cohomology(self) -> dict[tuple[int, int], list[int]]:
        degrees_to_compute = self.cohomology_degrees
        ret = {
            degree: h
            for degree in degrees_to_compute
            if (h := self.cohomology_in_degree(degree))
        }
        self.cohomology_computed = True
        return ret

    def cohomology_in_degree(self, degree: tuple[int, int]) -> list[int]:
        if self.cohomology_computed:
            return self.cohomology[degree]
        z = self.algebra.cocycles(degree).basis()
        b = self.algebra.coboundaries(degree).basis()
        if len(z) == len(b):
            return []
        character = []
        for g in self.class_representatives:
            matrix = self.act_on_basis(degree, g)
            character.append(trace_on_span(z, matrix) - trace_on_span(b, matrix))
        return character

    @cached_property
    def cohomology_dimension(self) -> dict[tuple[int, int], int]:
        ret = {
            degree: h
            for degree in self.cohomology_degrees
            if (h := self.cohomology_dimension_in_degree(degree))
        }
        self.cohomology_dimensions_computed = True
        return ret

    def cohomology_dimension_in_degree(self, degree: tuple[int, int]) -> int:
        if self.cohomology_dimensions_computed:
            return self.cohomology_dimension[degree]
        if self.cohomology_computed:
            return self.cohomology[degree][0]
        return self.algebra.cohomology(degree).dimension()

    @property
    def cohomology_degrees(self) -> Iterable[tuple[int, int]]:
        if self.cohomology_computed:
            return self.cohomology.keys()
        if self.cohomology_dimensions_computed:
            return self.cohomology_dimension.keys()
        return self.e2_page

    @overload
    def multiplicity(self, character: list[int], irrep: list[int]) -> int:
        ...

    @overload
    def multiplicity(self, character: list[int], irrep: None) -> list[int]:
        ...

    def multiplicity(
        self, character: list[int], irrep: list[int] | None = None
    ) -> int | list[int]:
        if irrep is None:
            return character
        irrep_decomposition = self.decompose_character(irrep)
        if len(irrep_decomposition) != 1:
            raise ValueError(f"{irrep} is not irreducible")
        irrep_character = irrep_decomposition[0][1]
        coefficient_iterator = (
            coefficient
            for coefficient, irrep2 in self.decompose_character(character)
            if irrep2 == irrep_character
        )
        return next(coefficient_iterator, 0)

    def act_on_generators(self, permutation: Callable[[int], int]) -> list[int]:
        ret = []
        for x, subscripts in self.generator_dict:
            new_subscripts = tuple(sorted(permutation(i + 1) - 1 for i in subscripts))
            ret.append(self.generator_list.index((x, new_subscripts)))
        return ret

    def act_on_basis(
        self, degree: tuple[int, int], generator_map: list[int]
    ) -> list[list[int]]:
        basis = self.algebra.basis(degree)
        if not basis:
            return []
        dimension = len(basis)
        matrix = [[0 for _ in range(dimension)] for _ in range(dimension)]
        for j, vector in enumerate(basis):
            image_vector = self.act_on_element(vector, generator_map)
            # print(vector, image_vector)
            for i, aij in enumerate(image_vector.basis_coefficients()):
                matrix[j][i] = aij  # matrix is list of columns
        return matrix

    def act_on_element(self, vector: Any, generator_map: list[int]) -> Any:
        return sum(
            self.act_on_term(generator_map, exponents, coefficient)
            for exponents, coefficient in vector.dict().items()
        )

    def act_on_term(
        self, generator_map: list[int], exponents: list[int], coefficient: int
    ) -> Any:
        ret = self.algebra(coefficient)
        for i in range(len(exponents)):
            ret *= (self.algebra.gens()[generator_map[i]]) ^ (exponents[i])
        return ret

    def decompose_character(self, character: list[int]) -> tuple[tuple[int, Any], ...]:
        return self.sn.character(character).decompose()


def complex_projective_space(dimension: int) -> Cohomology:
    diagonal = " + ".join(
        f"x{{i}}^{p}*x{{j}}^{dimension - p}" for p in range(dimension + 1)
    )
    return Cohomology(2 * dimension, {"x": 2}, [f"x^{dimension+1}"], diagonal)


# TODO: sign rep

# TODO: total cohomology

# TODO: TeX output
