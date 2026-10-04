import BalancedAssortments.ComplexityTimeTotalCertificates

/-! Executable smoke checks exercise malformed and illegal serialized inputs.
The valid examples deliberately use nonpositive target revenue. -/
namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityEncoding

private def sample (n K ap an ad hp hn hd rp rn rd vp vn vd : ℕ) : List Bool :=
  encodeFields [n,K,ap,an,ad,hp,hn,hd,rp,rn,rd,vp,vn,vd]
private def zeroWitness : List Bool := encodeFields [1,0,0,0,0]

#guard (totalVerify [] []).1 == false
#guard (totalVerify [true] zeroWitness).1 == false
#guard (totalVerify (sample 1 1 1 0 1 0 0 1 1 0 1 1 0 1) zeroWitness).1 == true
#guard (totalVerify (sample 1 1 1 0 1 0 2 1 1 0 1 1 0 1) zeroWitness).1 == true
-- Zero denominator, zero price, negative attraction.
#guard (totalVerify (sample 1 1 1 0 1 0 0 0 1 0 1 1 0 1) zeroWitness).1 == false
#guard (totalVerify (sample 1 1 1 0 1 0 0 1 0 0 1 1 0 1) zeroWitness).1 == false
#guard (totalVerify (sample 1 1 1 0 1 0 0 1 1 0 1 0 1 1) zeroWitness).1 == false
-- Balance parameter and cardinality outside their legal domains.
#guard (totalVerify (sample 1 1 0 0 1 0 0 1 1 0 1 1 0 1) zeroWitness).1 == false
#guard (totalVerify (sample 1 1 2 0 1 0 0 1 1 0 1 1 0 1) zeroWitness).1 == false
#guard (totalVerify (sample 1 0 1 0 1 0 0 1 1 0 1 1 0 1) zeroWitness).1 == false
#guard (totalVerify (sample 1 2 1 0 1 0 0 1 1 0 1 1 0 1) zeroWitness).1 == false
-- False header dimension and invalid certificate dimensions/denominator/mask.
#guard (totalVerify (sample 2 1 1 0 1 0 0 1 1 0 1 1 0 1) zeroWitness).1 == false
#guard (totalVerify (sample 1 1 1 0 1 0 0 1 1 0 1 1 0 1) (encodeFields [1,0])).1 == false
#guard (totalVerify (sample 1 1 1 0 1 0 0 1 1 0 1 1 0 1) (encodeFields [0,0,0,0,0])).1 == false
#guard (totalVerify (sample 1 1 1 0 1 0 0 1 1 0 1 1 0 1) (encodeFields [1,0,2,0,0])).1 == false

end BalancedAssortments.ComplexityTimeSourceParsing
