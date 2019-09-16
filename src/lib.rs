use std::fmt;
use std::ops::{Add, Sub, Mul, Div, Neg};

#[derive(Eq,PartialEq,Debug,Clone,Hash)]
pub struct IntMod {
    pub n: u32,
    prime: u32,
}

impl IntMod {
    pub fn new_from_i64(n: i64, prime: u32) -> IntMod {
        let p = prime as i64;
        let n = n % p ;
        let n = (if n < 0 {n + p} else {n}) as u32;
        IntMod::new(n, prime)
    }

    pub fn new(n: u32, prime: u32) -> IntMod {
        // TODO: add check to enforce prime argument
        let n = n % prime;
        IntMod{n, prime}
    }
}

impl fmt::Display for IntMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "integer_{}_mod_{}", self.n, self.prime)
    }
}

trait PowMod {
    fn pow_mod(self, exponent: u64, modulus: u32) -> Self;
}

pub trait Pow {
    fn pow(&self, exponent: i64) -> Self;
}

trait One {
    fn one(&self) -> Self;
}

trait Zero {
    fn zero(&self) -> Self;
}

impl PowMod for u32 {
    fn pow_mod(self: u32, exponent: u64, modulus: u32) -> u32 {
        let mut base = self;
        let mut exponent = exponent;
        if modulus == 1 { 0 }
        else {
            let mut result = 1;
            base = base % modulus;
            while exponent > 0 {
                if exponent % 2 == 1 {
                    result = (result * base) % modulus;
                }
                exponent = exponent >> 1;
                base = (base * base) % modulus;
            }
            result
        }
    }
}

impl Zero for IntMod {
    fn zero(&self) -> IntMod {
        return IntMod::new(0, self.n);
    }
}

impl One for IntMod {
    fn one(&self) -> IntMod {
        return IntMod::new(1, self.n);
    }
}

fn mod_add(this: &IntMod, other: &IntMod) -> IntMod {
    if this.prime != other.prime {panic!("Only IntMods with the same prime may be added.")}
    let checked_n = this.n.checked_add(other.n);
    let sum = match checked_n {
        Some(n) => {
            IntMod::new(n, this.prime)
        },
        None => {
            IntMod::new_from_i64((this.n as i64) + (other.n as i64), this.prime)
        }
    };
    return sum;
}

impl Add for IntMod {
    type Output = IntMod;
    fn add(self: IntMod, other: IntMod) -> IntMod {
        mod_add(&self, &other)
    }
}

impl<'a, 'b> Add<&'b IntMod> for &'a IntMod {
    type Output = IntMod;
    fn add(self: &'a IntMod, other: &'b IntMod) -> IntMod {
        mod_add(self, other)
    }
}

fn mod_sub(this: &IntMod, other: &IntMod) -> IntMod {
    if this.prime != other.prime {panic!("Only IntMods with the same prime may be subtracted.")}
    let checked_n = this.n.checked_sub(other.n);
    let difference = match checked_n {
        Some(n) => {
            IntMod::new(n, this.prime)
        },
        None => {
            IntMod::new_from_i64((this.n as i64) - (other.n as i64), this.prime)
        }
    };
    return difference;
}

impl Sub for IntMod {
    type Output = IntMod;
    fn sub(self, other: IntMod) -> IntMod {
        mod_sub(&self, &other)
    }
}

impl<'a, 'b> Sub<&'b IntMod> for &'a IntMod {
    type Output = IntMod;
    fn sub(self: &'a IntMod, other: &'b IntMod) -> IntMod {
        mod_sub(self, other)
    }
}

fn mod_mul(this: &IntMod, other: &IntMod) -> IntMod {
    if this.prime != other.prime {panic!("Only IntMods with the same prime may be multiplied.")}
    let checked_n = this.n.checked_mul(other.n);
    let product = match checked_n {
        Some(n) => {
            IntMod::new(n, this.prime)
        },
        None => {
            IntMod::new_from_i64((this.n as i64) * (other.n as i64), this.prime)
        }
    };
    return product;
}

impl Mul for IntMod {
    type Output = IntMod;
    fn mul(self, other: IntMod) -> IntMod {
        mod_mul(&self, &other)
    }
}

impl<'a, 'b> Mul<&'b IntMod> for &'a IntMod {
    type Output = IntMod;
    fn mul(self: &'a IntMod, other: &'b IntMod) -> IntMod {
        mod_mul(self, other)
    }
}

impl Pow for IntMod {
    fn pow(&self, exponent: i64) -> IntMod {
        let prime = self.prime as i64;
        let mut exponent = exponent % (prime - 1);
        if exponent < 0 {
            exponent += prime - 1
        };
        let exponent = exponent as u64;
        // TODO: consider changing signature of pow_mod to take u32 instead of u64 for exponent
        let power = self.n.pow_mod(exponent, self.prime);
        return IntMod::new(power, self.prime);
    }
}

fn mod_div(this: &IntMod, other: &IntMod) -> IntMod {
    if this.prime != other.prime {panic!("Only IntMods with the same prime may be divided.")}
    let prime = this.prime as i64;
    let dividend_inverse = other.pow( prime - 2);
    let quotient = this * &dividend_inverse;
    return quotient;
}

impl Div for IntMod {
    type Output = IntMod;
    fn div(self, other: IntMod) -> IntMod {
        mod_div(&self, &other)
    }
}

impl<'a, 'b> Div<&'b IntMod> for &'a IntMod {
    type Output = IntMod;
    fn div(self: &'a IntMod, other: &'b IntMod) -> IntMod {
        mod_div(self, other)
    }
}

impl Neg for IntMod {
    type Output = IntMod;
    fn neg(self) -> IntMod {
        return self;
    }
}


#[cfg(test)]
mod tests
{
    use super::IntMod;
    use super::PowMod;
    use super::Pow;

    #[test]
    fn int_mod_prime_1() {
        let n1 = IntMod::new(11, 7);
        let n2 = IntMod::new(4, 7);
        assert_eq!(n2, n1);
    }

    #[test]
    fn int_mod_prime_2() {
        let n1 = IntMod::new_from_i64(i64::min_value(), 7);
        let n2 = IntMod::new(6, 7);
        assert_eq!(n2, n1);
    }

    #[test]
    fn int_mod_prime_3() {
        let n1 = IntMod::new_from_i64(i64::max_value(), 7);
        let n2 = IntMod::new(0, 7);
        assert_eq!(n2, n1);
    }

    #[test]
    fn int_mod_prime_4() {
        let n1 = IntMod::new_from_i64(-1, 7);
        let n2 = IntMod::new(6, 7);
        assert_eq!(n2, n1);
    }

    #[test]
    fn int_mod_prime_5() {
        let n1 = IntMod::new_from_i64(-23, 7);
        let n2 = IntMod::new(5, 7);
        assert_eq!(n2, n1);
    }

    #[test]
    fn pow_mod_1() {
        let n: u32 = 4;
        let result = n.pow_mod(2, 3);
        assert_eq!(1, result);
    }

    #[test]
    fn pow_mod_2() {
        let n: u32 = 34;
        let result = n.pow_mod(456, 13);
        assert_eq!(1, result);
    }

    #[test]
    fn pow_mod_3() {
        let n: u32 = 12563;
        let result = n.pow_mod(69521, 57);
        assert_eq!(17, result);
    }

    #[test]
    fn pow_mod_4() {
        let n: u32 = 54;
        let result = n.pow_mod(u64::max_value(), 59);
        assert_eq!(6, result);
    }

    #[test]
    fn pow_mod_5() {
        let n: u32 = 54;
        let result = n.pow_mod(u32::max_value() as u64, 59);
        assert_eq!(8, result);
    }

    #[test]
    fn add_1() {
        let n1 = IntMod::new(5, 7);
        let n2 = IntMod::new(3, 7);
        let result = n1 + n2;
        assert_eq!(IntMod::new(1, 7), result);
        assert_eq!(1, result.n);
    }

    #[test]
    fn add_2() {
        let n1 = IntMod::new(9, 11);
        let n2 = IntMod::new(4, 11);
        let result = n1 + n2;
        assert_eq!(IntMod::new(2, 11), result);
        assert_eq!(2, result.n);
    }

    #[test]
    fn add_3() {
        let n1 = IntMod::new(u32::max_value(), 7);
        let n2 = IntMod::new(u32::max_value(), 7);
        let result = n1 + n2;
        assert_eq!(IntMod::new(6, 7), result);
        assert_eq!(6, result.n);
    }

    #[test]
    fn add_4() {
        let n1 = IntMod::new_from_i64(i64::min_value(), 7);
        let n2 = IntMod::new_from_i64(i64::min_value(), 7);
        let result = n1 + n2;
        assert_eq!(IntMod::new(5, 7), result);
        assert_eq!(5, result.n);
    }
    #[test]

    fn add_5() {
        let n1 = IntMod::new_from_i64(i64::max_value(), 7);
        let n2 = IntMod::new_from_i64(i64::max_value(), 7);
        let result = n1 + n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn add_6() {
        let n1 = IntMod::new(5, 7);
        let n2 = IntMod::new(3, 7);
        let n3 = IntMod::new(6, 7);
        let result1 = &n1 + &n2;
        let result2 = &n1 + &n3;
        let result3 = &n2 + &n3;
        assert_eq!(IntMod::new(1, 7), result1);
        assert_eq!(1, result1.n);
        assert_eq!(IntMod::new(4, 7), result2);
        assert_eq!(4, result2.n);
        assert_eq!(IntMod::new(2, 7), result3);
        assert_eq!(2, result3.n);
    }

    #[test]
    fn add_7() {
        let result1;
        {
            let n1 = IntMod::new(5, 7);
            let n2 = IntMod::new(3, 7);
            result1 = &n1 + &n2;
        }
        assert_eq!(IntMod::new(1, 7), result1);
        assert_eq!(1, result1.n);
    }

    #[test]
    fn sub_1() {
        let n1 = IntMod::new(5, 7);
        let n2 = IntMod::new(3, 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(2, 7), result);
        assert_eq!(2, result.n);
    }

    #[test]
    fn sub_2() {
        let n1 = IntMod::new(9, 7);
        let n2 = IntMod::new(4, 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(5, 7), result);
        assert_eq!(5, result.n);
    }

    #[test]
    fn sub_3() {
        let n1 = IntMod::new(u32::max_value(), 7);
        let n2 = IntMod::new(u32::max_value(), 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn sub_4() {
        let n1 = IntMod::new_from_i64(i64::min_value(), 7);
        let n2 = IntMod::new_from_i64(i64::min_value(), 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn sub_5() {
        let n1 = IntMod::new_from_i64(i64::max_value(), 7);
        let n2 = IntMod::new_from_i64(i64::max_value(), 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn sub_6() {
        let n1 = IntMod::new_from_i64(i64::max_value(), 7);
        let n2 = IntMod::new_from_i64(i64::min_value(), 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(1, 7), result);
        assert_eq!(1, result.n);
    }

    #[test]
    fn sub_7() {
        let n1 = IntMod::new_from_i64(i64::min_value(), 7);
        let n2 = IntMod::new_from_i64(i64::max_value(), 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(6, 7), result);
        assert_eq!(6, result.n);
    }

    #[test]
    fn sub_8() {
        let n1 = IntMod::new(3, 7);
        let n2 = IntMod::new(6, 7);
        let result = n1 - n2;
        assert_eq!(IntMod::new(4, 7), result);
        assert_eq!(4, result.n);
    }

    #[test]
    fn mul_1() {
        let n1 = IntMod::new(5, 7);
        let n2 = IntMod::new(3, 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(1, 7), result);
        assert_eq!(1, result.n);
    }

    #[test]
    fn mul_2() {
        let n1 = IntMod::new(9, 11);
        let n2 = IntMod::new(4, 11);
        let result = n1 * n2;
        assert_eq!(IntMod::new(3, 11), result);
        assert_eq!(3, result.n);
    }

    #[test]
    fn mul_3() {
        let n1 = IntMod::new(u32::max_value(), 7);
        let n2 = IntMod::new(u32::max_value(), 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(2, 7), result);
        assert_eq!(2, result.n);
    }

    #[test]
    fn mul_4() {
        let n1 = IntMod::new_from_i64(i64::min_value(), 7);
        let n2 = IntMod::new_from_i64(i64::min_value(), 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(1, 7), result);
        assert_eq!(1, result.n);
    }

    #[test]
    fn mul_5() {
        let n1 = IntMod::new_from_i64(i64::max_value(), 7);
        let n2 = IntMod::new_from_i64(i64::max_value(), 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn mul_6() {
        let n1 = IntMod::new_from_i64(i64::max_value(), 7);
        let n2 = IntMod::new_from_i64(i64::min_value(), 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn mul_7() {
        let n1 = IntMod::new_from_i64(i64::min_value(), 7);
        let n2 = IntMod::new_from_i64(i64::max_value(), 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(0, 7), result);
        assert_eq!(0, result.n);
    }

    #[test]
    fn mul_8() {
        let n1 = IntMod::new(3, 7);
        let n2 = IntMod::new(6, 7);
        let result = n1 * n2;
        assert_eq!(IntMod::new(4, 7), result);
        assert_eq!(4, result.n);
    }

    #[test]
    fn div_1() {
        let n1 = IntMod::new(3, 7);
        let n2 = IntMod::new(6, 7);
        let result = n1 / n2;
        assert_eq!(IntMod::new(4, 7), result);
        assert_eq!(4, result.n);
    }

    #[test]
    fn pow_1() {
        let n = IntMod::new(3, 7);
        let result = n.pow(2);
        assert_eq!(IntMod::new(2, 7), result);
        assert_eq!(2, result.n);
    }

    #[test]
    fn pow_2() {
        let n = IntMod::new(3, 7);
        let result = n.pow(4);
        assert_eq!(IntMod::new(4, 7), result);
        assert_eq!(4, result.n);
    }

    #[test]
    fn pow_3() {
        let n = IntMod::new(3, 7);
        let result = n.pow(-1);
        assert_eq!(IntMod::new(5, 7), result);
        assert_eq!(5, result.n);
    }

    #[test]
    fn pow_4() {
        let n = IntMod::new(6, 7);
        let result = n.pow(-2);
        assert_eq!(IntMod::new(1, 7), result);
        assert_eq!(1, result.n);
    }

    #[test]
    fn pow_5() {
        let n = IntMod::new(7, 11);
        let exponent = i64::max_value();
        let result = n.pow(exponent);
        assert_eq!(IntMod::new(6, 11), result);
        assert_eq!(6, result.n);
    }

    #[test]
    fn pow_6() {
        let n = IntMod::new(7, 11);
        let exponent = i64::min_value();
        let result = n.pow(exponent);
        assert_eq!(IntMod::new(5, 11), result);
        assert_eq!(5, result.n);
    }
}