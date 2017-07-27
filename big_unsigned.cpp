#include <iostream>
#include <string>
#include <vector>
#include <climits>
#include <cassert>
#include <utility>
#include <sstream>
#include <iomanip>
#include <numeric>

using namespace std;

// forward declarations
class big_u;
big_u operator*(const big_u &a, uint32_t b);
big_u operator*(const big_u &a, const big_u &b);
big_u operator+(const big_u &a, const big_u &b);
big_u operator-(const big_u &a, const big_u &b);

bool add_overflow_32(uint32_t a, uint32_t b) {
	return (a > UINT32_MAX - b);
}

bool mul_overflow_32(uint32_t a, uint32_t b) {
	return (a > UINT32_MAX / b);
}

uint32_t hi(uint64_t n) {
	return (uint32_t) (n >> 32);
}

uint32_t lo(uint64_t n) {
	return (uint32_t) (n & hi(UINT64_MAX));
}

/*
Multiplicative Carry Computation

1234 * 5678 = (1200 + 0034)*(5600 + 0078);
= 12 * 56 * 10000 + 12 * 78 * 100 + 34 * 56 * 100 + 34 * 78 
  --------          --------        --------        -------- 
  no carry          no carry        no carry        no carry 
= 0672 * 10000 + 0936 * 100 + 1904 * 100 + 2652
  ----           ----         ----         ----
  p3             p2           p1           p0
where
	p3 = hi(1234) * hi(5678)         
	p2 = hi(1234) * lo(5678)
	p1 = lo(1234) * hi(5678)
	p0 = lo(1234) * lo(5678)

= 0672 * 10000 + (0900 + 36) * 100 + (1900 + 04) * 100 + (2600 + 52)
= 0672 * 10000 + 09 * 10000 + 36 * 100 + 19 * 10000 + 04 * 100 + 26 * 100 + 52
= (0672 + 09 + 19) * 10000 + (36 + 04 + 26) * 100 + 52

= (p3 + hi(p2) + hi(p1)) * 10000
 +(lo(p2) + lo(p1) + hi(p0)) * 100
 +lo(p0)

the carry is therefore
(p3 + hi(p2) + hi(p1))
*/

uint64_t mul_carry(uint64_t a, uint64_t b) {
	uint64_t hi_a = hi(a);
	uint64_t hi_b = hi(b);
	uint64_t p3 = hi_a * hi_b;
	uint64_t p2 = hi_a * lo(b);
	uint64_t p1 = hi_b * lo(a);
	return p3 + hi(p2) + hi(p1);
}

// https://stackoverflow.com/a/5100745/4425924
template< typename T >
std::string int_to_hex( T i )
{
  std::stringstream stream;
  stream << std::setfill ('0') << std::setw(sizeof(T)*2) 
         << std::hex << i;
  return stream.str();
}

template <class T>
int cmp(const T&a, const T&b) {
	if (a < b) {return -1;}
	if (a > b) {return 1;}
	return 0;
}

// big unsigned integer
class big_u {
public:
    big_u(uint32_t n) : limbs({n}){}
    big_u(vector<uint32_t> limbs_) : limbs(limbs_) {}

    // little endian -- least significant
    // limb at lowest index
    std::vector<uint32_t> limbs;

    big_u &operator+=(const big_u &other) {
    	bool carry_in = false;
    	bool carry_out = false;
    	if (other.limbs.size() > this->limbs.size()) {
    		limbs.resize(other.limbs.size());
    	}
    	size_t i = 0;
    	while (i < other.limbs.size()) {
    		carry_out = add_overflow_32(limbs[i],other.limbs[i]);
    		limbs[i] += other.limbs[i];
    		if (carry_in) {
    			if (limbs[i] == UINT32_MAX - 1) {
    				carry_out = true;
    			}
    			++limbs[i];
    		}
    		++i;
    		carry_in = carry_out;
    		carry_out = false;
    	}
    	if (carry_in) {
    		if (!(limbs.size() > other.limbs.size())) {
    			limbs.push_back(1);
    		} else {
    			++limbs[i];
    		}
    	}
    	return *this;
    }


    /* Multiplication
    Consider s * t, where s is a 3-limb big_u and t is a 2-limb big_u
    Elementary multiplication:
	    	                    s2          s1          s0
	    	                            	t1          t0
	------------------------------------------------------
	          a[0][3]       a[0][2]    a[0][1]     a[0][0]
	a[1][4]   a[1][3]       a[1][2]    a[1][1]     a[1][0]

	where a values are computed as follows:
	carry = 0;
	current = s0t0 + carry;
	a[0][0] = lo(current);
	carry = hi(current);
	current = s1t0 + carry;
	a[0][1] == lo(current);
	carry = hi(current);
	etc...
	a[1][0] = 0;
	then repeat above procedure...

	The a[i][j] values are uint32_t's
	a[i] is a vector of uint32_t's --> a[i] is itself a big_u
	To compute the final result, simply add all the a[i]'s
    */

    // start with a many-by-one limb multiplication
    big_u &operator*=(uint32_t other) {
    	if (other == 0) {
    		limbs = {0};
    		return *this;
    	}
    	uint32_t carry = 0;
    	uint64_t current = 0;
    	uint64_t other_64 = other;
    	for (auto &limb : limbs) {
    		current = limb * other_64 + (uint64_t) carry;
    		limb = lo(current);
    		carry = hi(current);
    	}
    	if (carry > 0) {
    		limbs.push_back(carry);
    	}
    	return *this;
    }

    big_u &operator*=(const big_u &other) {
    	big_u current{0};
    	vector<big_u> a{};
    	vector<uint32_t> zero_limbs{};
    	for (int i = 0; i != other.limbs.size(); ++i) {
    		current = *this; // copy
    		current *= other.limbs[i];
    		current.limbs.insert(current.limbs.begin(),i,0);
    		a.push_back(current);
    	}
    	big_u result = std::accumulate(a.begin(),a.end(),big_u{0});
    	swap(result.limbs,this->limbs);
    	return *this;
    }

    // three-way comparison
    int cmp(const big_u &other) const {
    	if (this->limbs.size() != other.limbs.size()) {
    		return ::cmp(this->limbs.size(),other.limbs.size());
    	}
    	auto this_it = this->limbs.crbegin();
    	auto other_it = other.limbs.crbegin();
    	while (this_it != this->limbs.crend()) {
    		if (*this_it != *other_it) {
    			return ::cmp(*this_it,*other_it);
    		}
    		++this_it;
    		++other_it;
    	}
    	return 0;
    }

    // returns the complement of this relative to the 'next'
    // power of the radix
    // If our limbs were base ten digits, and this had
    // 3 limbs, say:
    // 184
    // then the complement is
    // 1000 - 184 = 999 - 184 + 1 = 815 + 1 = 816
    big_u complement() {
    	vector<uint32_t> out_limbs{};
    	for (auto limb : limbs) {
    		out_limbs.push_back(UINT32_MAX - limb);
    	}
    	big_u out{out_limbs};
    	out += big_u(1);
    	return out;
    }

    // subtraction
    // use radix-complement arithmetic
    // if limbs were base ten digits, and this == 465
    // other == 184
    // 465 - 184 == 465 + (1000 - 184) - 1000
    // this - other == this + other.complement() - 1000
    big_u &operator-=(big_u other) {
    	if (other > *this) {throw std::runtime_error("negative-result subtraction in unsigned type.");}
    	other.limbs.resize(this->limbs.size());
    	*this += other.complement();
    	
    	// debug
    	assert(this->limbs.back() == 1);

    	this->limbs.pop_back();
    	// there may now be leading zero limbs that
    	// must be removed
    	while (this->limbs.back() == 0 && this->limbs.size() > 1) {
    		this->limbs.pop_back();
    	}
    	return *this;
    }

    // returns this to the n power
    big_u pow(size_t n) {
    	if (n == 0) {return big_u{1};}
    	big_u out = *this;
    	size_t next_pow = 2;
    	// repeated squaring
    	while(next_pow <= n) {
    		out *= out;
    		next_pow *= 2;
    	}
    	size_t current_pow = next_pow / 2;
    	return out * this->pow(n - current_pow);
    }

    bool operator==(const big_u &other) const {
    	return this->cmp(other) == 0;
    }

    bool operator<(const big_u &other) const {
    	return this->cmp(other) == -1;
    }

    bool operator>(const big_u &other) {
    	return this->cmp(other) == 1;
    }

    string to_hex() const {
    	return "0x" + std::accumulate(limbs.rbegin(),limbs.rend(),string{},[](string cum, uint32_t next) {
    			return cum + int_to_hex(next);
    		}
    	);
    }
};

big_u operator+(const big_u &a, const big_u &b) {
	big_u out = a;
	out += b;
	return out;
}

big_u operator-(const big_u &a, const big_u &b) {
	big_u out = a;
	out -= b;
	return out;
}

big_u operator*(const big_u &a, uint32_t b) {
	big_u out = a;
	return out *= b;
}

big_u operator*(const big_u &a, const big_u &b) {
	big_u out = a;
	return out *= b;
}

void test_equals() {
	assert(big_u(0) == big_u(0));
	assert(big_u(1) == big_u(1));
	assert(big_u(UINT32_MAX) == big_u(UINT32_MAX));
	assert(big_u({0,1}) == big_u({0,1}));
}

void test_plus() {
	big_u a = big_u(0);
	a += big_u(1);
	assert(a == big_u(1));
	assert(big_u(1) + big_u(2) == big_u(3));
	assert(big_u(UINT32_MAX) + big_u(1) == big_u({0,1}));
	assert(big_u(UINT32_MAX) + big_u(UINT32_MAX) == big_u({UINT32_MAX - 1,1}));

	// 0x89abcdef01234567 + 0x0123456789abcdefafafafaf == 0x0123456813579bdeb0d2f516
	big_u b{{0x01234567,0x89abcdef}}; //0x89abcdef01234567
	big_u c{{0xafafafaf,0x89abcdef,0x01234567}}; //0x0123456789abcdefafafafaf
	big_u d{{0xb0d2f516,0x13579bde,0x01234568}}; //0x0123456813579bdeb0d2f516
	assert(b + c == d);
}

void test_hi_lo() {
	uint64_t n = UINT64_MAX;
	assert(hi(n) == 0xFFFFFFFF);
	assert(lo(n) == 0xFFFFFFFF);
	assert(hi(0xFFFFFFFF) == 0);
	assert(lo(0xFFFFFFFF) == 0xFFFFFFFF);
	assert(hi(0x100000000) == 1);
	assert(lo(0x100000000) == 0);
}

void test_str() {
	big_u a{0xFFFFFFFF};
	assert(a.to_hex() == "0xffffffff");
	big_u b{0};
	assert(b.to_hex() == "0x00000000");
	big_u c{{0x98765432,0x12345678}};
	assert(c.to_hex() == "0x1234567898765432");
}

void test_mul() {
	big_u a{6};
	a *= 0;
	assert(a == big_u{0});
	big_u b{2};
	big_u three{3};
	big_u six{6};
	b *= 3;
	assert(b == six);
	big_u c{0xFFFFFFFF};
	c *= 0xFFFFFFFF;
	assert(c == big_u({0x00000001,0xFFFFFFFE}));
	assert(big_u(0) * big_u(0) == big_u(0));
	assert(big_u(1) * big_u(2) == big_u(2));
	assert(c * c == big_u({0x00000001,0xfffffffc,0x00000005,0xfffffffc}));
	big_u d{{0x89abcdef,0x01234567}};
	big_u e{{0x76543210,0xfedcba98}};
	big_u f = d * e;
	assert(f == big_u({0xe5618cf0,0x2236d88f,0xad77d742,0x0121fa00}));
	assert(f.to_hex() == "0x0121fa00ad77d7422236d88fe5618cf0");
}

void test_cmp() {
	big_u one{1};
	assert(one > big_u{0});
	assert(one == big_u{1});
	assert(one < big_u{2});

	big_u a{0xFFFFFFFF};
	big_u b{{0x00000000,0xFFFFFFFE}};
	big_u c{{0x00000001,0xFFFFFFFE}};
	big_u d{{0x00000000,0xFFFFFFFF}};
	big_u e{{0x00000001,0xFFFFFFFF}};
	big_u f{{0x00000001,0xFFFFFFFF}};

	assert(a < b);
	assert(b < c);
	assert(c < d);
	assert(d < e);
	assert(e == f);
}

void test_complement() {
	assert(big_u(1).complement() == big_u(UINT32_MAX));
}

void test_minus() {
	big_u zero{0};
	big_u one{1};
	assert(one - one == zero);
	assert(one - zero == one);

	big_u b{{0x01234567,0x89abcdef}}; //0x89abcdef01234567
	big_u c{{0xafafafaf,0x89abcdef,0x01234567}}; //0x0123456789abcdefafafafaf
	big_u d{{0xb0d2f516,0x13579bde,0x01234568}}; //0x0123456813579bdeb0d2f516
	assert(b + c == d);
	assert(d - c == b);
	assert(d - b == c);

}

void test_pow() {
	big_u two{2};
	assert(two.pow(0) == big_u(1));
	assert(two.pow(1) == big_u(2));
	assert(two.pow(10) == big_u(1024));

	big_u a{0x89abcdef};
	big_u b{{0xa1fb3b61,0x8457af45,0xf3c34186,0xdc58bda1,0xf39bbf71,0x06313f53}}; //0x06313f53 f39bbf71 dc58bda1 f3c34186 8457af45 a1fb3b61
	
	assert(a.pow(6).to_hex() == "0x06313f53f39bbf71dc58bda1f3c341868457af45a1fb3b61");
	assert(b.to_hex() == "0x06313f53f39bbf71dc58bda1f3c341868457af45a1fb3b61");
	assert(a.pow(6) == b);
}	

int main() {
	test_equals();
	test_plus();
	test_hi_lo();
	test_str();
	test_mul();
	test_cmp();
	test_complement();
	test_minus();
	test_pow();
}

