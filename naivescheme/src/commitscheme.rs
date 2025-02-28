use rand::{ Rng, thread_rng };
use rand::prelude::SliceRandom;
use rand_core::{ CryptoRng, RngCore, OsRng };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT, constants::RISTRETTO_BASEPOINT_TABLE };
use zeroize::Zeroize; 
use sha2::{ Sha512, Digest }; 
use std::io;
use std::io::{ IoSlice, Write };
use std::fs::File;
use std::fs;
use std::io::Read;
use curve25519_dalek::ristretto::CompressedRistretto;


// Definition of the structure for the setup set:
#[derive(Clone, Debug, PartialEq)]
pub struct Set { 
    pub gen: RistrettoPoint,  
    pub h_: RistrettoPoint, 
    pub n1: usize,
    pub n2: usize 
}
 
// Definition of the structure for the commitment:
#[derive(Clone, Debug, PartialEq)]
pub struct Commit { 
    pub cstar: RistrettoPoint,
    pub c: Vec<RistrettoPoint>
}

// Definition of the structure for the zero-knowledge proof in the algorithm "Commit":
#[derive(Clone, Debug, PartialEq)]
pub struct ZeroKnowledgeProofCommit {
    pub proofcom0: ProofofPartialKnowledge,
    pub proofcom1: Vec<ProofofPartialKnowledge>
}
#[derive(Clone, Debug, PartialEq)]
pub struct ProofofPartialKnowledge {
    pub commitments: Vec<RistrettoPoint>,
    pub challenge: Scalar,
    pub responses: Vec<Scalar>,
    pub interpolated_polynomial: Vec<Scalar>
}

// Definition of the structure for the zero-knowledge proof in the algorithm "Open":
#[derive(Clone, Debug, PartialEq)]
pub struct ZeroKnowledgeProofOpen {
    pub commitment: RistrettoPoint,
    pub response: Scalar
}

// Definition of the structure for the signature:
#[derive(Debug)]
pub struct Signature {
    pub r: RistrettoPoint,
    pub z: Scalar
}

// Generate a random Scalar element:
pub fn rand_scalar<T: CryptoRng + RngCore>(rng: &mut T) -> Scalar {
    let mut scalar_bytes = [0u8; 64];
    rng.fill_bytes(&mut scalar_bytes);
    Scalar::from_bytes_mod_order_wide(&scalar_bytes)
}
   
// Generate a random RistrettoPoint element:
pub fn rand_element<T: CryptoRng + RngCore>(rng: & mut T) -> RistrettoPoint {   
    let r = rand_scalar(rng);
    let g = &r * RISTRETTO_BASEPOINT_TABLE;
    return g;
}

// Generate a random vector of bit of size l:
pub fn rand_bitstring (l: usize) -> Vec<usize> {
    let mut v: Vec<usize> = Vec::new();
    let mut rng = thread_rng(); 
    for _i in 0..l {
        if rng.gen_bool(0.5) == true {
            v.push(0);      
        }
       	else {
	    v.push(1); 
        }
    }
    return v;
}

// Initialize a vector of Scalar of size l:
fn init_vec_scalar(t: usize) -> Vec<Scalar> {   
    let vec = vec![convert_scalar([0u8; 32]); t];
    return vec;
}

// Initialize a vector of RistrettoPoint::identity() of size l:
fn init_vec_ristretto(l: usize) -> Vec<RistrettoPoint> {
    let vec = vec![RistrettoPoint::identity(); l];
    return vec;
}

// Convert a [u8; 32] in Scalar:
fn convert_scalar(a: [u8; 32]) -> Scalar {   
    let s = Scalar::from_bytes_mod_order(a);
    return s
}

// Hash a vector of bytes:
pub fn hash(digest: Vec<[u8;32]>) -> Scalar {

    let mut hasher = <Sha512 as Digest>::new();

    for d in digest {
        hasher.update(d.as_slice());
    }

    let result = hasher.finalize();
    Scalar::from_bytes_mod_order_wide(&result.into())
}

// Generate a random message between two values:
pub fn rand_message(a : usize, b: usize) -> u64 {
    let mut rng = thread_rng();
    let m: u64 = rng.gen_range(a..=b) as u64;
    return m;
}

// Generate a random permutation of vector:
pub fn rand_permutation(len : usize) -> Vec<usize> { 
    let mut v: Vec<usize> = (0..len).collect();
    let mut rng = thread_rng();
    v.shuffle(&mut rng);
    return v;
}

// Convert a usize to an array [u8; 32]:
pub fn usize_to_u8_array(u: usize) -> [u8; 32] {
    let mut array: [u8; 32] = [0u8; 32];
    let bytes = u.to_le_bytes();

    for i in 0..bytes.len() {
        array[i] = bytes[i];
    }
    
    return array;
}

// Convert an array [u8; 32] to a usize:
pub fn u8_array_to_usize(array: [u8; 32]) -> usize {
    let bytes = &array[0..8]; 
    let u = usize::from_le_bytes(bytes.try_into().expect("REASON"));
    
    return u;
}

//Lagrange
// Multiplies two polynomials represented as vectors of Scalars.
fn multiply_polynomials(poly1: &[Scalar], poly2: &[Scalar]) -> Vec<Scalar> {

    let mut result = vec![Scalar::from(0u64); poly1.len() + poly2.len() - 1];

    for (i, &coeff1) in poly1.iter().enumerate() {
        for (j, &coeff2) in poly2.iter().enumerate() {
            result[i + j] += coeff1 * coeff2;
        }
    }
    return result;
}

// Computes the Lagrange basis polynomial for a given set of x_values at index k.
fn lagrange_basis_polynomial(x_values: &[Scalar], k: usize) -> Vec<Scalar> {

    let mut numerator = vec![Scalar::from(1u64)];
    let mut denominator = Scalar::from(1u64);

    for (j, &x_j) in x_values.iter().enumerate() {
        if j != k {
            numerator = multiply_polynomials(&numerator, &[Scalar::from(0u64) - x_j, Scalar::from(1u64)]);
            denominator *= x_values[k] - x_j;
        }
    }
    
    numerator.iter_mut().for_each(|coeff| *coeff *= denominator.invert());
    
    return numerator;
}

// Computes the Lagrange interpolation polynomial for the given set of x_values and y_values.
fn lagrange_interpolation_polynomial(x_values: &[Scalar], y_values: &[Scalar]) -> Vec<Scalar> {
    assert!(x_values.len() == y_values.len(), "x_values and y_values must have the same length");

    let mut result = vec![Scalar::from(0u64); x_values.len()];

    for (k, &y_k) in y_values.iter().enumerate() {
        let basis_poly = lagrange_basis_polynomial(x_values, k);
        for (i, coeff) in basis_poly.iter().enumerate() {
            if i < result.len() {
                result[i] += y_k * coeff;
            } 
            else {
                result.push(y_k * coeff);
            }
        }
    }

    return result;
}

// Evaluates a polynomial at a given x.
fn evaluate_polynomial(coefficients: &[Scalar], x: Scalar) -> Scalar {
    let mut result = Scalar::from(0u64);
    let mut x_power = Scalar::from(1u64);

    for &coeff in coefficients {
        result += coeff * x_power;
        x_power *= x;
    }

    return result;
}

// Returns the degree of a polynomial represented by a vector of Scalars.
fn polynomial_degree(coefficients: &[Scalar]) -> usize {
    for i in (0..coefficients.len()).rev() {
        if coefficients[i] != Scalar::from(0u64) {
            return i;
        }
    }
    0 // If all coefficients are zero, return degree 0.
}

/*// Displays a polynomial represented by a vector of Scalars.

// Converts a Scalar to a u64 integer.
fn scalar_to_u64(scalar: &Scalar) -> u64 {
    let bytes = scalar.to_bytes();
    let mut array = [0u8; 8];
    array.copy_from_slice(&bytes[0..8]);
    u64::from_le_bytes(array)
}

fn display_polynomial(coefficients: &[Scalar]) -> String {
    let mut terms = Vec::new();

    for (i, coeff) in coefficients.iter().enumerate() {
        if *coeff != Scalar::from(0u64) {
            let coeff_str = if i == 0 || *coeff != Scalar::from(1u64) {
                format!("{}", scalar_to_u64(&coeff))
            } else {
                String::new() // Do not display "1" for x^1
            };

            let term = match i {
                0 => format!("{}", coeff_str),
                1 => format!("{}x", coeff_str),
                _ => format!("{}x^{}", coeff_str, i),
            };

            terms.push(term);
        }
    }

    if terms.is_empty() {
        "0".to_string()
    } 
    else {
        terms.join(" + ")
    }
}*/

// Proof of partial knowledge:
pub fn prove_partial_knowledge<T: CryptoRng + RngCore>(rng: &mut T, g: Vec<RistrettoPoint>, y: Vec<RistrettoPoint>, t: Vec<Scalar>, trueinstance: Vec<bool>) -> ProofofPartialKnowledge { 
    
    let mut vec_com = init_vec_ristretto(g.len());
    let mut vec_chal = init_vec_scalar(g.len());
    let mut vec_resp = init_vec_scalar(g.len());   
    let mut vec_random = init_vec_scalar(g.len());
          
    for i in 0..g.len() {
    	// Commitment for the verified instances:
    	if trueinstance[i] == true {
            let random = rand_scalar(rng);
            vec_random[i] = random; 
    	    vec_com[i] = random * g[i];
    	}
    	else {
    	    // Simulation:
      	    // Challenges for the unverified instance:
      	    vec_chal[i] = rand_scalar(rng);
            
       	    // Responses for the unverified instance:
       	    vec_resp[i] = rand_scalar(rng);
            
            // Commitments for the unverified instance:
            vec_com[i] = vec_resp[i] * g[i] - vec_chal[i] * y[i];
        }	     	
    }
    
    // Challenge of the proof:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    for i in 0..g.len() {
        prehash.push(*(g[i].compress()).as_bytes());
    } 
    for i in 0..vec_com.len() {  
    	prehash.push(*(vec_com[i].compress()).as_bytes());  
    }
         
    let chal_0 = hash(prehash); 
        
    // Construct the lagrange polynomial
    let mut a_values: Vec<Scalar> = Vec::new();
    let mut b_values: Vec<Scalar> = Vec::new();
    a_values.push(Scalar::from(0u64));
    b_values.push(chal_0);

    for i in 0..g.len() {
    	if trueinstance[i] == false {
    	    a_values.push(Scalar::from((i+1) as u64));
    	    b_values.push(vec_chal[i]);
    	}
    }

    let poly = lagrange_interpolation_polynomial(&a_values, &b_values);
     
    for i in 0..g.len(){
    	if trueinstance[i] == true{
    	    // Challenges for the verified instance:
    	    vec_chal[i] = evaluate_polynomial(&poly,Scalar::from((i+1) as u64));
          
    	    // Responses for the verified instance:
    	    vec_resp[i] = vec_random[i] + t[i] * vec_chal[i];
        }
    }
    vec_random.zeroize();
            
    return ProofofPartialKnowledge{ commitments: vec_com, challenge: chal_0, responses: vec_resp, interpolated_polynomial: poly };
}

// Verification of the ProofofPartialKnowledge:
pub fn verify_partial_knowledge(g: Vec<RistrettoPoint>, y: Vec<RistrettoPoint>, t: usize, proof_partial: ProofofPartialKnowledge) -> bool {

    // Parse the proof:
    let com = proof_partial.commitments;
    let chal_0 = proof_partial.challenge;
    let resp = proof_partial.responses;
    let poly = proof_partial.interpolated_polynomial;
    
    if polynomial_degree(&poly) == t && chal_0 == evaluate_polynomial(&poly,Scalar::from(0u64)) {
    	for i in 0..g.len() {
    	    if resp[i] * g[i] != com[i] + evaluate_polynomial(&poly,Scalar::from((i+1) as u64)) * y[i] {
    	    	return false
    	    }  
    	}
    }
    else {
    	return false
    }
    return true
}

// Zero-Knowledge Proof for Open:
pub fn prove_open<T: CryptoRng + RngCore>(rng: &mut T, g: RistrettoPoint, y: RistrettoPoint, k: Scalar) -> ZeroKnowledgeProofOpen { 
    
    // Commitment for the instance "AND":
    let mut random = rand_scalar(rng);
    let com = random * g;
	
    // Challenge of the proof:  	
    let chal = hash(vec![*(g.compress()).as_bytes(), *(y.compress()).as_bytes(), *(com.compress()).as_bytes()]);
    
    // Response for the instance "AND":
    let resp = random + k * chal;
    
    random.zeroize();

    return ZeroKnowledgeProofOpen { commitment: com, response: resp };  
}

// Verification of the Zero-Knowledge Proof Open:
pub fn verify_open(g: RistrettoPoint, y: RistrettoPoint, proof_open: ZeroKnowledgeProofOpen) -> bool {
	
    // Parse the proof:
    let com = proof_open.commitment;
    let resp = proof_open.response;

    // Challenge of proof: 
    let chal = hash(vec![*(g.compress()).as_bytes(), *(y.compress()).as_bytes(), *(com.compress()).as_bytes()]);
	
    // Test:
    if resp * g - chal * y != com {
	    return false;
    }
    return true;
}

// Generate a setup set:
pub fn setup<T: CryptoRng + RngCore>(rng: &mut T, n_1: usize, n_2: usize) -> Set {
    let generator = RISTRETTO_BASEPOINT_POINT;
    let h = rand_element(rng);
    let set = Set{ gen: generator, h_: h, n1: n_1, n2: n_2 };  
    return set;   
}

// Generate a commitment for a message m:
pub fn commit<T: CryptoRng + RngCore>(rng: &mut T, set: Set, m: u64, theta: Vec<usize>) -> ((u64, Scalar, Vec<Scalar>), Commit, ZeroKnowledgeProofCommit) {

    // Parse set:
    let generator = set.gen;
    let h = set.h_;
    let n_1 = set.n1;
    let n_2 = set.n2;
    
    // Generate key k_star:
    let k_star = rand_scalar(rng);
    
    // Commit m:
    let msg = Scalar::from(m);
    let c_star = msg * generator + k_star * h; // commit the original message m.
    
    // Construct vector v:
    let range: Vec<u64> = (0..=n_1-1).map(|x| x as u64).collect();
    let mut v: Vec<u64> = Vec::new();
    for i in range {
    	if i == m {
    	    v.extend(vec![i; n_1+n_2-1]); // add n1 + n2 - 1 times m.
    	}
    	else {
    	    v.extend(vec![i; n_1-1]); // add n1 - 1 times values != m.
    	}
    }
    // Apply the permutation theta to the vector v:
    let mut v_permut: Vec<u64> = vec![0 as u64; n_1*n_2];
    for i in 0..n_1*n_2 {
    	v_permut[i] = v[theta[i]];
    }

    // Generate key k:  
    let mut k: Vec<Scalar> = Vec::new();
    for _i in 0..n_1*n_2 { 
        k.push(rand_scalar(rng));
    }
    
    // Commit each element of v:
    let mut c: Vec<RistrettoPoint> = Vec::new();
    for i in 0..n_1*n_2 {
    	c.push(Scalar::from(v_permut[i]) * generator + k[i] * h);  
    }
      
    // Proof that m is committed at least n1 + n2 - 1 times in c_star:
    let mut cc: Vec<RistrettoPoint> = Vec::new(); // cc[i] = c_star - c[i]
    let mut kk: Vec<Scalar> = Vec::new(); // kk[i] = k_star - k[i]
    let mut trueinstance_0: Vec<bool> = Vec::new();
    for i in 0..c.len() {
    	cc.push(c_star - c[i]);
    	kk.push(k_star - k[i]);
    	if cc[i] == (kk[i]) * h {
    	   trueinstance_0.push(true);  	  
    	}
    	else {
    	   trueinstance_0.push(false);
    	}
    }
    
    let proof_commit_0 = prove_partial_knowledge(rng, vec![h; n_1*n_2], cc , kk, trueinstance_0);
    
    // Proof that each values i in [0, ..., n2 - 1] is committed at least n1 - 1 times in c:
    let mut ccc: Vec<RistrettoPoint> = init_vec_ristretto(c.len()); //ccc[i] = c_star - c[i]
    let mut proof_commit_1: Vec<ProofofPartialKnowledge> = Vec::new();
    let mut trueinstance_1: Vec<bool> = vec![false; c.len()];
    for i in 0..n_2 {
        let mut s1 = 0;
        for j in 0..c.len() {
    	    ccc[j] = c[j] - Scalar::from(i as u64) * generator;
            if ccc[j] == k[j] * h && s1 < n_1-1{
    	        trueinstance_1[j] = true;
    	        s1 +=1;
    	    }
    	    else {
    	   	trueinstance_1[j] = false;
    	    }
    	}
    	
    	proof_commit_1.push(prove_partial_knowledge(rng, vec![h; n_1*n_2], ccc.clone() , k.clone(), trueinstance_1.clone()));
    	
    }	
    
    let proof_commit = ZeroKnowledgeProofCommit{ proofcom0: proof_commit_0, proofcom1: proof_commit_1 };
    let key = (m, k_star, k);
    let com = Commit{ cstar: c_star, c: c };
    return (key, com, proof_commit)
}

// Verify the proof of commitment:
pub fn ver_commit(set: Set, com: Commit, proof_commit: ZeroKnowledgeProofCommit) -> bool { 
    
    // Parse set:
    let generator = set.gen;
    let h = set.h_;
    let n_1 = set.n1;
    let n_2 = set.n2;
    
    // Parse c:
    let c_star = com.cstar;
    let c = com.c;
    
    // Parse proof_com:
    let proof_commit_0 = proof_commit.proofcom0;
    let proof_commit_1 = proof_commit.proofcom1;
    
    let t0 = n_1*n_2-(n_1+n_2-1); // corresponds to the degree of the polynomial.
    let mut cc: Vec<RistrettoPoint> = Vec::new(); //cc[i] = c_star - c[i].
    for i in 0..c.len() {
    	cc.push(c_star - c[i]);
    }
    
    // Verify the proof that m is committed at least n1 + n2 - 1 times in c_star.
    let b0 = verify_partial_knowledge(vec![h; n_1*n_2], cc, t0, proof_commit_0);
    if b0 == false {
        return false
    }
    else {	
        // Verify the proofs that each i is committed at least n1 - 1 times in c.
        let t1 = n_1*n_2-(n_1-1); // corresponds to the degree of the polynomial.
    	let mut ccc: Vec<RistrettoPoint> = init_vec_ristretto(c.len()); //ccc[i] = c_star - c[i].
    	for i in 0..n_2 {
            for j in 0..c.len() {
    	        ccc[j] = c[j] - Scalar::from(i as u64) * generator;
    	    }
	    if verify_partial_knowledge(vec![h; n_1 * n_2], ccc.clone(), t1, proof_commit_1[i].clone()) == false {
	        return false
            }
        }
    }
    return true  
}

// Open the commitment:
pub fn open<T: CryptoRng + RngCore>(rng: &mut T, set: Set, key: (u64, Scalar, Vec<Scalar>), com: Commit) -> (u64, ZeroKnowledgeProofOpen) {
	
    // Parse set:
    let generator = set.gen;
    let h = set.h_;
	
    // Parse k:
    let m = key.0;
    let k_star = key.1;
    	
    // Parse c:
    let c_star = com.cstar;

   // Convert m:
    let msg = Scalar::from(m);
    
    let gm = msg * generator;
    
    let proof_open = prove_open(rng, h, c_star - gm, k_star);
     	
    return (m, proof_open);
}

// Verify the opening:
pub fn ver_open(set: Set, com: Commit, m: u64, proof_open: ZeroKnowledgeProofOpen) -> bool {

    // Parse set:
    let g = set.gen;
    let h = set.h_;
	
    // Parse com:
    let c_star = com.cstar;
    
    // Convert m:
    let msg = Scalar::from(m);
    
    let gm = msg * g;
    
    return verify_open(h, c_star - gm, proof_open);	
}

// Open the commitment with LDP:
pub fn openldp<T: CryptoRng + RngCore>(rng: &mut T, set: Set, key: (u64, Scalar, Vec<Scalar>), com: Commit, hat_theta: usize) -> (u64, ZeroKnowledgeProofOpen){
	
    // Parse set:
    let generator = set.gen;
    let h = set.h_;
    
    // Parse key:
    let k = &key.2;
    
    // Parse com:
    let c = com.c;

    let mut i: usize = 0;
    while c[hat_theta] != Scalar::from(i as u64) * generator + k[hat_theta] * h {
        i += 1;
    }
    let hat_m = i as u64;
    
    let ghatm = Scalar::from(hat_m) * generator;
    
    let proof_openldp = prove_open(rng, h, c[hat_theta] - ghatm, k[hat_theta]);
	
    return (hat_m, proof_openldp);	
}	

// Verify the opening with LDP:
pub fn ver_openldp(set: Set, com: Commit, hat_m: u64
, proof_openldp: ZeroKnowledgeProofOpen, hat_theta: usize) -> bool {

    // Parse set:
    let generator = set.gen;
    let h = set.h_;
	
    // Parse com:
    let c = com.c;
    
    let ghatm = Scalar::from(hat_m) * generator;
    
    return verify_open(h, c[hat_theta] - ghatm, proof_openldp); 
}

// Generate a public secret key:
pub fn gen<T: CryptoRng + RngCore>(rng: &mut T, g: RistrettoPoint) -> (Scalar, RistrettoPoint) {
    let secret_key = rand_scalar(rng);
    let public_key = secret_key * g;
    return (secret_key, public_key);
}

// Generate a signature of Commitment:
pub fn sign<T: CryptoRng + RngCore>(rng: &mut T, com: Commit, g: RistrettoPoint, pubk: RistrettoPoint, secretk: Scalar) -> Signature {

    let mut rand = rand_scalar(rng);
    let r_ = rand * g;
	
    // Challenge:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    prehash.push(*(g.compress()).as_bytes());
    prehash.push(*(pubk.compress()).as_bytes());
    prehash.push(*(r_.compress()).as_bytes());
    prehash.push(*(com.cstar.compress()).as_bytes());
    for i in 0..com.c.len() {
    	prehash.push(*(com.c[i].compress()).as_bytes());
    }
    
    let chal = hash(prehash);
	
    // Response:
    let z_ = rand + chal * secretk;
	
    rand.zeroize();
	
    return Signature{ r: r_, z: z_ };
}

// Verify the signature:
pub fn ver(com: Commit, g: RistrettoPoint, pubk: RistrettoPoint, s: Signature) -> bool {

    let r_ = s.r;
    let z_ = s.z;
	
    // Challenge:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    prehash.push(*(g.compress()).as_bytes());
    prehash.push(*(pubk.compress()).as_bytes());
    prehash.push(*(r_.compress()).as_bytes());
    prehash.push(*(com.cstar.compress()).as_bytes());
    for i in 0..com.c.len() {
    	prehash.push(*(com.c[i].compress()).as_bytes());
    }
    
    let chal = hash(prehash);
	
    // Test:
    if r_ == z_ * g - chal * pubk {
	return true;
    }
    return false;
}

// Write the setup in a file:
fn writesetup(set: &Set) -> io::Result<()> {
    let mut setup: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("setup.txt")?;
    match set{
    	Set{ gen, h_, n1, n2 } => {
    	    setup.push(((gen).compress()).to_bytes());
    	    setup.push(((h_).compress()).to_bytes());
            setup.push(usize_to_u8_array(*n1));
    	    setup.push(usize_to_u8_array(*n2));
        },
    }
    for i in 0..setup.len() {
        file.write_vectored(&[IoSlice::new(&setup[i])])?;
    }
    return Ok(())
} 

// Export the setup located in a file:
fn exportsetup() -> Set {
    let mut buffer = Vec::new();
    let file = File::open("setup.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut setup : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len() {
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0 {
    		setup.push(array.clone());
    	}
    }
    let generator = CompressedRistretto(setup[0]).decompress().unwrap();
    let h = CompressedRistretto(setup[1]).decompress().unwrap();
    let n_1 = u8_array_to_usize(setup[2]);
    let n_2 = u8_array_to_usize(setup[3]);
    return Set{ gen: generator, h_: h, n1: n_1, n2: n_2 };
}

// Write the commitment in a file:
fn writecommit(com: &Commit) -> io::Result<()> {
    let mut commit: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("commitment.txt")?;
    match com {
    	Commit{	cstar, c } => {
    	    commit.push(((cstar).compress()).to_bytes());
    	    for i in 0..c.len() {
    	        commit.push(((c[i]).compress()).to_bytes());		    
    	    }
        },
    }
    for i in 0..commit.len() {
        file.write_vectored(&[IoSlice::new(&commit[i])])?;
    }
    return Ok(())
}    

// Read the commitment located in a file.
fn exportcommit(n1: usize, n2: usize) -> Commit {
    let mut buffer = Vec::new();
    let file = File::open("commitment.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut commit : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len() {
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0 {
    		commit.push(array.clone());
    	}
    }
    let c_star = CompressedRistretto(commit[0]).decompress().unwrap();
    let mut com: Vec<RistrettoPoint> = Vec::new();
    for i in 1.. n1*n2 + 1 {
    	com.push(CompressedRistretto(commit[i]).decompress().unwrap());
    }
    return Commit{ cstar: c_star, c: com };
}

// Write the proof of commitment in a file:
fn writeproofcommit(p: &ZeroKnowledgeProofCommit, n2: usize) -> io::Result<()> {
    let mut proof: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("proofcommitment.txt")?;
    match p {
        ZeroKnowledgeProofCommit{ proofcom0, proofcom1 } => {
            match &proofcom0 { // proof that m is committed at least n1 + n2 - 1 times in c_star.
                 ProofofPartialKnowledge{ commitments, challenge, responses, interpolated_polynomial } => { 
                    for j in 0..commitments.len() {
                        proof.push(((commitments[j]).compress()).to_bytes());
                    }
                    proof.push(challenge.to_bytes());
                    for j in 0..responses.len() {
                        proof.push(responses[j].to_bytes());
                    }
                    for j in 0..interpolated_polynomial.len() {
                        proof.push(interpolated_polynomial[j].to_bytes());
                    }
                }
            }
            for i in 0..n2 {
                match &proofcom1[i] { //proof that each value is committed at least n1 - 1 times in c.
                    ProofofPartialKnowledge{ commitments, challenge, responses, interpolated_polynomial } => { 
                        for j in 0..commitments.len() {
                            proof.push(((commitments[j]).compress()).to_bytes());
                        }
                        proof.push(challenge.to_bytes());
                        for j in 0..responses.len() {
                            proof.push(responses[j].to_bytes());
                        }
                        for j in 0..interpolated_polynomial.len() {
                            proof.push(interpolated_polynomial[j].to_bytes());
                        }                     
                    }
                }
            }
        }
    }
                 
    for k in 0..proof.len() {
        file.write_vectored(&[IoSlice::new(&proof[k])])?;
    }
    return Ok(())
}

// Read the proof of commitment located in a file.
fn exportproofcommit(n1: usize, n2: usize) -> ZeroKnowledgeProofCommit {
    let mut buffer = Vec::new();
    let file = File::open("proofcommitment.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut p : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len(){
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0 {
    		p.push(array.clone());
    	}
    }
    let t0 = n1*n2-(n1+n2-1)+1;
    let t1 = n1*n2-(n1-1)+1;
    let mut compt = 0;
    
    // Proof that m is committed at least n1 + n2 - 1 times in c_star:
    let mut com0: Vec<RistrettoPoint> = Vec::new();
    let mut resp0: Vec<Scalar> = Vec::new();
    let mut poly0: Vec<Scalar> = Vec::new();
    for j in compt..compt + n1*n2 {
        com0.push(CompressedRistretto(p[j]).decompress().unwrap());
    }
    compt = compt + n1*n2;
    let chal0 = Scalar::from_bytes_mod_order(p[compt]);
    compt += 1;
    for j in compt..compt + n1*n2 {
        resp0.push(Scalar::from_bytes_mod_order(p[j]));
    }
    compt = compt + n1*n2;
    for j in compt..compt + t0 {
        poly0.push(Scalar::from_bytes_mod_order(p[j]));
    }
    compt = compt + t0;
    
    let proof0 = ProofofPartialKnowledge{ commitments: com0, challenge: chal0, responses: resp0, interpolated_polynomial: poly0 };
    
     // Proof that each value is committed at least n1 - 1 times in c:
    let mut proof1: Vec<ProofofPartialKnowledge> = Vec::new();
    
    for _i in 0..n2 {
        let mut com1: Vec<RistrettoPoint> = Vec::new();
        let mut resp1: Vec<Scalar> = Vec::new();
        let mut poly1: Vec<Scalar> = Vec::new();
    	for j in compt..compt + n1*n2 {
            com1.push(CompressedRistretto(p[j]).decompress().unwrap());
        }
        compt = compt + n1*n2;
        let chal1 = Scalar::from_bytes_mod_order(p[compt]);
        compt += 1;
        for j in compt..compt + n1*n2 {
            resp1.push(Scalar::from_bytes_mod_order(p[j]));
        }
        compt = compt + n1*n2;
        for j in compt..compt + t1 {
            poly1.push(Scalar::from_bytes_mod_order(p[j]));
        }
        compt = compt + t1;
        proof1.push(ProofofPartialKnowledge{ commitments: com1, challenge: chal1, responses: resp1, interpolated_polynomial: poly1 });
    }

    return ZeroKnowledgeProofCommit { proofcom0: proof0, proofcom1: proof1 };  
} 

// Write the proof of opening in a file:
fn writeproofopen(p: &ZeroKnowledgeProofOpen) -> io::Result<()> {
    let mut proof: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("proofopening.txt")?;
    
    match p {
    	ZeroKnowledgeProofOpen{ commitment, response } => {
    	    proof.push((commitment.compress()).to_bytes());
    	    proof.push((response).to_bytes());
    	}
    }	    
    for k in 0..proof.len(){
        file.write_vectored(&[IoSlice::new(&proof[k])])?;
    }
    return Ok(())
} 

// Read the proof of opening located in a file.
fn exportproofopen() -> ZeroKnowledgeProofOpen {
    let mut buffer = Vec::new();
    let file = File::open("proofopening.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut p : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len(){
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0 {
    		p.push(array.clone());
    	}
    }
    let r = CompressedRistretto(p[0]).decompress().unwrap();
    let z = Scalar::from_bytes_mod_order(p[1]);
    
    return ZeroKnowledgeProofOpen{ commitment: r, response: z };
}


// Write the proof of opening in a file:
fn writeproofopenldp(p: &ZeroKnowledgeProofOpen) -> io::Result<()> {
    let mut proof: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("proofopeningldp.txt")?;
    
    match p {
    	ZeroKnowledgeProofOpen{ commitment, response } => {
    	    proof.push((commitment.compress()).to_bytes());
    	    proof.push((response).to_bytes());
    	}
    }	    
    for k in 0..proof.len(){
        file.write_vectored(&[IoSlice::new(&proof[k])])?;
    }
    return Ok(())
} 

// Read the proof of opening located in a file.
fn exportproofopenldp() -> ZeroKnowledgeProofOpen {
    let mut buffer = Vec::new();
    let file = File::open("proofopeningldp.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut p : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len() {
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0{
    		p.push(array.clone());
    	}
    }
    let r = CompressedRistretto(p[0]).decompress().unwrap();
    let z = Scalar::from_bytes_mod_order(p[1]);
    
    return ZeroKnowledgeProofOpen{ commitment: r, response: z };
}

// Functions for measuring the elapsed time between each algorithm:
pub fn measure_time(iter: u32, n_1: usize, n_2: usize) {

    let mut time_setup = Duration::ZERO;
    let mut time_commit = Duration::ZERO;
    let mut time_ver_commit = Duration::ZERO;
    let mut time_open = Duration::ZERO;
    let mut time_ver_open = Duration::ZERO;
    let mut time_openldp = Duration::ZERO;
    let mut time_ver_openldp = Duration::ZERO;
    let mut time_gen = Duration::ZERO;
    let mut time_sig = Duration::ZERO;
    let mut time_ver_sig = Duration::ZERO;
      
    let mut setsize = 0;  
    let mut comsize = 0;
    let mut pcomsize = 0;
    let mut popensize = 0;
    let mut popenldpsize = 0;

    for _i in 0..iter {
	
	let mut csrng = OsRng; 
    
    	// Setup:
    	let start_setup = Instant::now();
   	let set = setup(&mut csrng, n_1, n_2);  
   	let duration_setup = start_setup.elapsed();
   	time_setup += duration_setup;
   	
   	
   	let _ = writesetup(&set);
        let newset = exportsetup();
        assert!(newset == set, "The setup in the file in not equal to the real setup");
    	let setdata = fs::metadata("setup.txt");
    	setsize += setdata.expect("REASON").len();
   		
    	let theta = rand_permutation(n_1 * n_2);
    	let m = rand_message(0, n_2 - 1);
    	
    	// Commit:
    	let start_commit = Instant::now();
    	let comm = commit(&mut csrng, set.clone(), m, theta);
    	let duration_commit = start_commit.elapsed();
   	time_commit += duration_commit;
   	
    	let k = comm.0;
    	let c = comm.1;
    	let p_comm = comm.2;
    	  	
    	// Be careful: the sizes can be large
    	if n_1 <= 32 && n_2 <= 32 {
    	    let _ = writecommit(&c);
            let newc = exportcommit(n_1, n_2);
            assert!(newc == c, "The commitment in the file in not equal to the real commitment");
    	    let comdata = fs::metadata("commitment.txt");
    	    comsize += comdata.expect("REASON").len();
    	
    	    let _ = writeproofcommit(&p_comm, n_2);
            let new_pcomm = exportproofcommit(n_1, n_2);
            assert!(new_pcomm == p_comm, "The proof of commitment in the file in not equal to the real proof of commitment");
    	    let pcomdata = fs::metadata("proofcommitment.txt");
    	    pcomsize += pcomdata.expect("REASON").len();
    	}
    	
    	// Ver_Commit:
    	let start_ver_commit = Instant::now();
    	let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
    	let duration_ver_commit = start_ver_commit.elapsed();
    	time_ver_commit += duration_ver_commit;
    	
    	assert!(b_comm == true, "Ver_Commit != 1 \n");
    
    	// Open:
    	let start_open = Instant::now();
    	let opening = open(&mut csrng, set.clone(), k.clone(), c.clone());
    	let duration_open = start_open.elapsed();
    	time_open += duration_open;
  
    	let m_open = opening.0;
    	let p_open = opening.1;
    	
    	let _ = writeproofopen(&p_open);
        let new_popen = exportproofopen();
        assert!(new_popen == p_open, "The proof of opening in the file in not equal to the real proof of opening");
    	let popendata = fs::metadata("proofopening.txt");
    	popensize += popendata.expect("REASON").len();
    	
    	// Ver_Open:
    	let start_ver_open = Instant::now();
    	let b_open = ver_open(set.clone(), c.clone(), m.clone(), p_open);
    	let duration_ver_open = start_ver_open.elapsed();
    	time_ver_open += duration_ver_open;
	
    	assert!(m == m_open, "The opened message is not equal to the original message \n");
    	assert!(b_open == true, "Ver_Open != 1 \n");
    
	// Openldp:
	let mut rng = thread_rng(); 
	let hat_theta: usize = rng.gen_range(0..=n_1 * n_2 - 1);
    	
    	let start_openldp = Instant::now();
    	let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), hat_theta);
    	let duration_openldp = start_openldp.elapsed();
    	time_openldp += duration_openldp;
    	
    	let hat_m = openingldp.0;
    	let p_openldp = openingldp.1;
    	
    	let _ = writeproofopenldp(&p_openldp);
        let new_popenldp = exportproofopenldp();
        assert!(new_popenldp == p_openldp, "The proof of opening with ldp in the file in not equal to the real proof of opening with ldp");
    	let popenldpdata = fs::metadata("proofopeningldp.txt");
    	popenldpsize += popenldpdata.expect("REASON").len();
    	
    	// Ver_Openldp:
    	let start_ver_openldp = Instant::now();
    	let b_openldp = ver_openldp(set.clone(), c.clone(), hat_m, p_openldp, hat_theta);
    	let duration_ver_openldp = start_ver_openldp.elapsed();
    	time_ver_openldp += duration_ver_openldp;
    	
    	assert!(b_openldp == true, "Ver_Openldp != 1 \n"); 
    	
    	// Schnorr's Signature:
    	
    	// Gen:
    	let start_gen = Instant::now();
	let (secret_key, public_key) = gen(&mut csrng, RISTRETTO_BASEPOINT_POINT);
	let duration_gen = start_gen.elapsed();
	time_gen += duration_gen;

	// Sign:
	let start_sig = Instant::now();
	let sig = sign(&mut csrng, c.clone(), RISTRETTO_BASEPOINT_POINT, public_key, secret_key);
	let duration_sig = start_sig.elapsed();
	time_sig += duration_sig;

	// Verify the Signature:   	    	
	let start_ver_sig = Instant::now();
	let verify = ver(c.clone(), RISTRETTO_BASEPOINT_POINT, public_key, sig);
	let duration_ver_sig = start_ver_sig.elapsed();
	time_ver_sig += duration_ver_sig;
			
	assert!(verify == true, "Ver != 1 \n"); 
    }
    
    let average_time_setup = time_setup/iter.try_into().unwrap();
    let average_time_commit = time_commit/iter.try_into().unwrap();
    let average_time_ver_commit = time_ver_commit/iter.try_into().unwrap();
    let average_time_open = time_open/iter.try_into().unwrap();
    let average_time_ver_open = time_ver_open/iter.try_into().unwrap();
    let average_time_openldp = time_openldp/iter.try_into().unwrap();
    let average_time_ver_openldp = time_ver_openldp/iter.try_into().unwrap();
    let average_time_gen = time_gen/iter.try_into().unwrap();
    let average_time_sig = time_sig/iter.try_into().unwrap();
    let average_time_ver_sig = time_ver_sig/iter.try_into().unwrap();
    
    let averagesetsize = setsize/u64::from(iter);
    let averagecomsize = comsize/u64::from(iter);
    let averagepcomsize = pcomsize/u64::from(iter);
    let averagepopensize = popensize/u64::from(iter);
    let averagepopenldpsize = popenldpsize/u64::from(iter);
    
    println!("Average running time over {:?} iterations with n1 = {:?} and n2 = {:?}:", iter, n_1, n_2);
    println!("LDP Commitment scheme:");
    print!("Setup: {:?} \n", average_time_setup);
    print!("Commit: {:?} \n", average_time_commit);
    print!("Ver_Commit: {:?} \n", average_time_ver_commit);
    print!("Open: {:?} \n", average_time_open);     
    print!("Ver_Open: {:?} \n", average_time_ver_open);
    print!("OpenLDP: {:?} \n", average_time_openldp);
    print!("Ver_OpenLDP: {:?} \n", average_time_ver_openldp);
   
    print!("Size of setup: {:?} bytes \n", averagesetsize); 
    print!("Size of commitment: {:?} bytes \n", averagecomsize);
    print!("Size of proof of commitment: {:?} bytes \n", averagepcomsize);
    print!("Size of proof of opening: {:?} bytes \n", averagepopensize);
    print!("Size of proof of opening with ldp: {:?} bytes \n", averagepopenldpsize);
    
    println!("Schnorr signature of commitment:");
    print!("Gen: {:?} \n", average_time_gen);
    print!("Sign: {:?} \n", average_time_sig);
    print!("Ver: {:?} \n", average_time_ver_sig);
}
