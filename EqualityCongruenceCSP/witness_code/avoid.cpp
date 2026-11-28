// Exact arithmetic subroutine for avoiding finitely many affine hyperplanes.
// This program is not a Taylor CSP solver. See README.md for its precise scope.
// Tested build:
// g++ -std=c++17 -O2 -Wall -Wextra -pedantic -DAVOID_USE_GMP avoid.cpp -lgmpxx -lgmp -o avoid
// Optional Boost build (requires Boost headers):
// g++ -std=c++17 -O2 -Wall -Wextra -pedantic avoid.cpp -o avoid

#ifdef AVOID_USE_GMP
#include <gmpxx.h>
#else
#include <boost/multiprecision/cpp_int.hpp>
#endif

#include <cstddef>
#include <exception>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#ifdef AVOID_USE_GMP
using Integer = mpz_class;
#else
using Integer = boost::multiprecision::cpp_int;
#endif
using Vector = std::vector<Integer>;
using Matrix = std::vector<Vector>;

struct AffineForm {
    Integer constant;
    Vector linear;
};

struct Instance {
    std::size_t n;
    std::size_t d;
    std::size_t h;
    Integer modulus;
    Vector origin;
    Matrix basis;
    Vector residue;
    std::vector<AffineForm> forms;
};

Integer read_integer(const std::string& label) {
    std::string token;
    if (!(std::cin >> token)) {
        throw std::invalid_argument("missing integer for " + label);
    }
    std::size_t position = 0;
    bool negative = false;
    if (token[position] == '+' || token[position] == '-') {
        negative = token[position] == '-';
        ++position;
    }
    if (position == token.size()) {
        throw std::invalid_argument("invalid decimal integer for " + label);
    }
    Integer value = 0;
    for (; position < token.size(); ++position) {
        const char digit = token[position];
        if (digit < '0' || digit > '9') {
            throw std::invalid_argument("invalid decimal integer for " + label);
        }
        value *= 10;
        value += digit - '0';
    }
    return negative ? -value : value;
}

std::size_t read_dimension(const std::string& label) {
    const Integer value = read_integer(label);
    const Integer maximum = std::numeric_limits<std::size_t>::max();
    if (value < 0 || value > maximum) {
        throw std::invalid_argument("dimension out of range for " + label);
    }
    std::stringstream stream;
    stream << value;
    std::size_t result = 0;
    if (!(stream >> result)) {
        throw std::invalid_argument("dimension conversion failed for " + label);
    }
    return result;
}

Instance read_instance() {
    Instance input;
    input.n = read_dimension("n");
    input.d = read_dimension("d");
    input.h = read_dimension("h");
    input.modulus = read_integer("m");
    if (input.modulus <= 0) {
        throw std::invalid_argument("m must be positive");
    }
    input.origin.resize(input.n);
    for (Integer& value : input.origin) {
        value = read_integer("u");
    }
    input.basis.assign(input.n, Vector(input.d));
    for (Vector& row : input.basis) {
        for (Integer& value : row) {
            value = read_integer("B");
        }
    }
    input.residue.resize(input.d);
    for (Integer& value : input.residue) {
        value = read_integer("rho");
    }
    input.forms.reserve(input.h);
    for (std::size_t j = 0; j < input.h; ++j) {
        AffineForm form;
        form.constant = read_integer("form constant");
        form.linear.resize(input.n);
        for (Integer& value : form.linear) {
            value = read_integer("form coefficient");
        }
        input.forms.push_back(std::move(form));
    }
    std::string extra;
    if (std::cin >> extra) {
        throw std::invalid_argument("extra token after the last affine form");
    }
    return input;
}

Integer evaluate(const AffineForm& form, const Vector& point) {
    Integer value = form.constant;
    for (std::size_t i = 0; i < point.size(); ++i) {
        value += form.linear[i] * point[i];
    }
    return value;
}

Vector make_point(const Instance& input, const Vector& parameters) {
    Vector point = input.origin;
    for (std::size_t i = 0; i < input.n; ++i) {
        for (std::size_t j = 0; j < input.d; ++j) {
            point[i] += input.basis[i][j] * parameters[j];
        }
    }
    return point;
}

void print_vector(const std::string& label, const Vector& values) {
    std::cout << label << ' ' << values.size();
    for (const Integer& value : values) {
        std::cout << ' ' << value;
    }
    std::cout << '\n';
}

bool verify_returned_point(const Instance& input, const Vector& base,
                           const Vector& z, const Vector& parameters,
                           const Vector& point, const Vector& values) {
    // Verify using base + m B z rather than the construction u + B parameters.
    // This is an exact output check; it does not establish CSP satisfiability.
    for (std::size_t j = 0; j < input.d; ++j) {
        if (parameters[j] - input.residue[j] != input.modulus * z[j]) {
            return false;
        }
    }
    for (std::size_t i = 0; i < input.n; ++i) {
        Integer expected = base[i];
        for (std::size_t j = 0; j < input.d; ++j) {
            expected += input.modulus * input.basis[i][j] * z[j];
        }
        if (point[i] != expected) {
            return false;
        }
    }
    for (std::size_t j = 0; j < input.h; ++j) {
        const Integer checked_value = evaluate(input.forms[j], point);
        if (values[j] != checked_value || checked_value == 0) {
            return false;
        }
    }
    return true;
}

int solve(const Instance& input) {
    const Vector base = make_point(input, input.residue);
    for (std::size_t j = 0; j < input.h; ++j) {
        const Integer intercept = evaluate(input.forms[j], base);
        Vector slopes(input.d, 0);
        bool identically_zero = intercept == 0;
        for (std::size_t k = 0; k < input.d; ++k) {
            for (std::size_t i = 0; i < input.n; ++i) {
                slopes[k] += input.modulus * input.forms[j].linear[i]
                             * input.basis[i][k];
            }
            if (slopes[k] != 0) {
                identically_zero = false;
            }
        }
        if (identically_zero) {
            std::cout << "IDENTICALLY_ZERO " << j << '\n';
            std::cout << "BASE_VALUE " << intercept << '\n';
            print_vector("DIRECTION_VALUES", slopes);
            return 2;
        }
    }

    // Arbitrary precision prevents overflow in the candidate bound h*d.
    const Integer bound = Integer(input.h) * Integer(input.d);
    for (Integer candidate = 0; candidate <= bound; ++candidate) {
        Vector z(input.d);
        Vector parameters(input.d);
        Integer power = candidate;
        for (std::size_t j = 0; j < input.d; ++j) {
            z[j] = power;  // Exponents are 1,...,d, never 0,...,d-1.
            parameters[j] = input.residue[j] + input.modulus * z[j];
            power *= candidate;
        }
        const Vector point = make_point(input, parameters);
        Vector values(input.h);
        bool valid = true;
        for (std::size_t j = 0; j < input.h; ++j) {
            values[j] = evaluate(input.forms[j], point);
            if (values[j] == 0) {
                valid = false;
            }
        }
        if (valid) {
            if (!verify_returned_point(input, base, z, parameters, point, values)) {
                throw std::logic_error("exact verification of the point failed");
            }
            std::cout << "OK\n";
            std::cout << "T " << candidate << '\n';
            std::cout << "BOUND " << bound << '\n';
            print_vector("Z", z);
            print_vector("PARAMETERS", parameters);
            print_vector("X", point);
            print_vector("VALUES", values);
            std::cout << "VERIFIED exact_coset_and_nonzero_forms\n";
            return 0;
        }
    }
    throw std::logic_error("root bound violated: no valid candidate in 0,...,h*d");
}

int main() {
    try {
        const Instance input = read_instance();
        return solve(input);
    } catch (const std::invalid_argument& error) {
        std::cerr << "INPUT_ERROR " << error.what() << '\n';
        return 64;
    } catch (const std::exception& error) {
        std::cerr << "INTERNAL_ERROR " << error.what() << '\n';
        return 70;
    }
}
