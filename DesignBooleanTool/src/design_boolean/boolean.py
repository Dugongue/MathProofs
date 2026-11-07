"""Small, dependency-free Boolean-function value type; bit zero is x0."""
from dataclasses import dataclass
from numbers import Integral

@dataclass(frozen=True)
class BooleanFunction:
    truth_table: tuple[int, ...]

    def __post_init__(self):
        values = tuple(self.truth_table)
        if not values or len(values) & (len(values)-1):
            raise ValueError("Truth-table length must be a positive power of two.")
        if any(not isinstance(v, Integral) or v not in (0, 1) for v in values):
            raise ValueError("Truth-table values must be integer bits.")
        object.__setattr__(self, "truth_table", tuple(int(v) for v in values))

    @property
    def num_variables(self):
        return len(self.truth_table).bit_length()-1

    def __call__(self, x):
        if not isinstance(x, Integral) or not 0 <= x < len(self.truth_table):
            raise ValueError("Input must be an integer truth-table index in range.")
        return self.truth_table[int(x)]

    def walsh_spectrum(self):
        values = [1-2*v for v in self.truth_table]
        step = 1
        while step < len(values):
            for start in range(0,len(values),2*step):
                for j in range(start,start+step):
                    a,b = values[j],values[j+step]
                    values[j],values[j+step] = a+b,a-b
            step *= 2
        return values

    def anf_terms(self):
        """Monomial bit masks; mask 0 denotes the constant one."""
        coeff = list(self.truth_table)
        for i in range(self.num_variables):
            bit = 1 << i
            for mask in range(len(coeff)):
                if mask & bit:
                    coeff[mask] ^= coeff[mask ^ bit]
        return [mask for mask,value in enumerate(coeff) if value]

    def anf(self):
        terms = []
        for mask in self.anf_terms():
            terms.append("*".join(f"x{i}" for i in range(self.num_variables) if mask >> i & 1) or "1")
        return " + ".join(terms) or "0"

    @property
    def nonlinearity(self):
        return (len(self.truth_table)-max(map(abs,self.walsh_spectrum())))//2

    def to_dict(self):
        spectrum = self.walsh_spectrum()
        magnitudes = sorted({abs(v) for v in spectrum if v})
        return {"num_variables": self.num_variables, "bit_order": "little-endian; index = sum(x_i * 2**i)",
                "truth_table": list(self.truth_table), "anf": self.anf(),
                "anf_terms": self.anf_terms(), "walsh_magnitudes": magnitudes,
                "nonlinearity": (len(self.truth_table)-max(map(abs,spectrum)))//2}

    def to_sage(self):
        """Convert inside SageMath, if installed; Sage is an optional dependency."""
        from sage.crypto.boolean_function import BooleanFunction as SageBooleanFunction
        return SageBooleanFunction(list(self.truth_table))
