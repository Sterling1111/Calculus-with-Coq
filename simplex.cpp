#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <cctype>
#include <stdexcept>
#include <Eigen/Dense>
#include <boost/rational.hpp>
#include <boost/multiprecision/cpp_int.hpp>

using BigInt = boost::multiprecision::cpp_int;
using Rational = boost::rational<BigInt>;

template<> struct Eigen::NumTraits<Rational> : Eigen::NumTraits<double> {
    typedef Rational Real;
    typedef Rational NonInteger;
    typedef Rational Nested;
    enum { IsComplex = 0, IsInteger = 0, IsSigned = 1, RequireInitialization = 1, ReadCost = 1, AddCost = 1, MulCost = 1 };
};

typedef Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic> MatrixXR;
typedef std::map<int, int> Row;

BigInt gcd(BigInt a, BigInt b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        BigInt t = b;
        b = a % b;
        a = t;
    }
    return a;
}

BigInt lcm(BigInt a, BigInt b) {
    if (a == 0 || b == 0) return 0;
    return (a / gcd(a, b)) * b;
}

void skipWhitespace(const std::string& s, size_t& pos) {
    while (pos < s.length() && std::isspace(s[pos])) pos++;
}

void match(const std::string& s, size_t& pos, const std::string& target) {
    skipWhitespace(s, pos);
    if (s.substr(pos, target.length()) == target) pos += target.length();
    skipWhitespace(s, pos);
}

int parseNum(const std::string& s, size_t& pos) {
    skipWhitespace(s, pos);
    int sign = 1;
    if (pos < s.length() && s[pos] == '-') { sign = -1; pos++; }
    int res = 0;
    while (pos < s.length() && std::isdigit(s[pos])) res = res * 10 + (s[pos++] - '0');
    skipWhitespace(s, pos);
    return res * sign;
}

Row addRows(const Row& a, const Row& b) {
    Row res = a;
    for (auto const& [var, coeff] : b) res[var] += coeff;
    return res;
}

Row multRows(const Row& a, const Row& b) {
    bool a_is_const = (a.empty() || (a.size() == 1 && a.count(0)));
    bool b_is_const = (b.empty() || (b.size() == 1 && b.count(0)));
    if (!a_is_const && !b_is_const) throw std::runtime_error("Non-linear equation detected");
    
    Row res;
    if (a_is_const) {
        int c = a.count(0) ? a.at(0) : 0;
        for (auto const& [var, coeff] : b) res[var] = c * coeff;
    } else {
        int c = b.count(0) ? b.at(0) : 0;
        for (auto const& [var, coeff] : a) res[var] = coeff * c;
    }
    return res;
}

Row parseRow(const std::string& s, size_t& pos) {
    skipWhitespace(s, pos);
    if (s.substr(pos, 4) == "Var(") {
        match(s, pos, "Var(");
        int v = parseNum(s, pos);
        match(s, pos, ")");
        Row r; r[v] = 1; return r;
    } else if (s.substr(pos, 6) == "Const(") {
        match(s, pos, "Const(");
        int c = parseNum(s, pos);
        match(s, pos, ")");
        Row r; if (c != 0) r[0] = c; return r;
    } else if (s.substr(pos, 4) == "Neg(") {
        match(s, pos, "Neg(");
        Row r = parseRow(s, pos);
        match(s, pos, ")");
        Row res; for (auto const& [v, c] : r) res[v] = -c; return res;
    } else if (s.substr(pos, 4) == "Add(") {
        match(s, pos, "Add(");
        Row left = parseRow(s, pos);
        match(s, pos, ",");
        Row right = parseRow(s, pos);
        match(s, pos, ")");
        return addRows(left, right);
    } else if (s.substr(pos, 5) == "Mult(") {
        match(s, pos, "Mult(");
        Row left = parseRow(s, pos);
        match(s, pos, ",");
        Row right = parseRow(s, pos);
        match(s, pos, ")");
        return multRows(left, right);
    }
    throw std::runtime_error("Parse error at position " + std::to_string(pos) + " for string: " + s);
}

class SimplexSolver {
private:
    MatrixXR D;
    std::vector<int> dep_vars;
    std::vector<int> col_vars;
    int n, m;
    std::vector<Rational> multipliers;

    void pivot(int p_row, int p_col) {
        Rational a = D(p_row, p_col);
        D(p_row, p_col) = Rational(-1);
        for (int j = 0; j < D.cols(); ++j) D(p_row, j) /= -a;

        for (int i = 0; i <= m; ++i) {
            if (i != p_row) {
                Rational factor = D(i, p_col);
                D(i, p_col) = Rational(0);
                for (int j = 0; j < D.cols(); ++j) D(i, j) += factor * D(p_row, j);
            }
        }
        
        int leaving_var = dep_vars[p_row - 1];
        int entering_var = col_vars[p_col - 1];
        dep_vars[p_row - 1] = entering_var;
        col_vars[p_col - 1] = leaving_var;
    }

    void solve_loop() {
        while (true) {
            int p_col = -1;
            for (int j = 1; j <= n + 1; ++j) {
                if (D(0, j) < 0) {
                    p_col = j;
                    break;
                }
            }

            if (p_col == -1) break;

            int p_row = -1;
            Rational min_ratio(-1);
            int min_dep = -1;

            for (int i = 1; i <= m; ++i) {
                if (D(i, p_col) < 0) {
                    Rational ratio = -D(i, 0) / D(i, p_col);
                    if (p_row == -1 || ratio < min_ratio || 
                       (ratio == min_ratio && dep_vars[i - 1] < min_dep)) {
                        min_ratio = ratio;
                        p_row = i;
                        min_dep = dep_vars[i - 1];
                    }
                }
            }

            if (p_row == -1) throw std::runtime_error("Unbounded");
            pivot(p_row, p_col);
        }
    }

public:
    SimplexSolver(const MatrixXR& c, const MatrixXR& A, const MatrixXR& b) {
        n = c.rows();
        m = A.rows();
        
        D = MatrixXR::Zero(m + 1, n + m + 2);

        for (int j = 0; j < n; ++j) D(0, j + 1) = c(j, 0);
        for (int i = 0; i < m; ++i) D(i + 1, 0) = b(i, 0);
        
        for (int j = 1; j <= n; ++j) col_vars.push_back(j - 1);
        col_vars.push_back(n); 

        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < n; ++j) D(i + 1, j + 1) = -A(i, j);
            D(i + 1, n + 1) = Rational(1); 
            D(i + 1, n + 2 + i) = Rational(-1);
            dep_vars.push_back(n + 1 + i); 
        }
    }

    void solve() {
        int min_row = -1;
        Rational min_b(0);
        for (int i = 1; i <= m; ++i) {
            if (D(i, 0) < min_b) {
                min_b = D(i, 0);
                min_row = i;
            }
        }

        if (min_row != -1) {
            MatrixXR orig_obj = D.row(0);
            D.row(0).setZero();
            D(0, n + 1) = Rational(1); 

            pivot(min_row, n + 1);
            solve_loop();

            if (D(0, 0) > Rational(0)) {
                for (int i = 0; i < m; ++i) multipliers.push_back(D(0, n + 2 + i));
                throw std::runtime_error("Contradiction");
            }
        } else {
            solve_loop();
        }
    }

    std::string get_result_string() {
        std::ostringstream oss;
        if (!multipliers.empty()) {
            BigInt L = 1;
            for (const auto& m_val : multipliers) {
                if (m_val.numerator() != 0) {
                    L = lcm(L, m_val.denominator());
                }
            }
            oss << "Multipliers: [ ";
            for (const auto& m_val : multipliers) {
                BigInt v = (m_val.numerator() * L) / m_val.denominator();
                oss << v << " ";
            }
            oss << "]";
            return oss.str();
        }
        oss << "Optimal Value: " << D(0, 0);
        return oss.str();
    }
};

int main(int argc, char* argv[]) {
    if (argc != 3) return 1;

    std::ifstream infile(argv[1]);
    std::ofstream outfile(argv[2]);
    
    std::vector<Row> parsed_rows;
    std::string line;
    
    try {
        int max_var = 0;
        while (std::getline(infile, line)) {
            if (!line.empty()) {
                size_t pos = 0;
                Row r = parseRow(line, pos);
                for (auto const& [v, c] : r) {
                    if (v > max_var) max_var = v;
                }
                parsed_rows.push_back(r);
            }
        }

        int m = parsed_rows.size();
        int n = max_var; 
        
        MatrixXR A = MatrixXR::Zero(m, 2 * n);
        MatrixXR b = MatrixXR::Zero(m, 1);
        MatrixXR c = MatrixXR::Zero(2 * n, 1);

        for (int i = 0; i < m; ++i) {
            for (auto const& [v, coeff] : parsed_rows[i]) {
                if (v == 0) b(i, 0) = Rational(-coeff);
                else {
                    A(i, v - 1) = Rational(coeff);
                    A(i, n + v - 1) = Rational(-coeff);
                }
            }
        }

        SimplexSolver solver(c, A, b);
        try {
            solver.solve();
            outfile << solver.get_result_string() << "\n";
        } catch (const std::runtime_error& e) {
            std::string msg = e.what();
            if (msg == "Contradiction") {
                outfile << solver.get_result_string() << "\n";
            } else {
                outfile << "Error: " << msg << "\n";
            }
        }
        
    } catch (const std::exception& e) {
        outfile << "Error: " << e.what() << "\n";
    }

    return 0;
}