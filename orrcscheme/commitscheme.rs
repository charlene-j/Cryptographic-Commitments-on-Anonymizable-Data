use rand::{ Rng, thread_rng };
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
    pub g_: Vec<Vec<RistrettoPoint>>, 
    pub f_: Vec<Vec<RistrettoPoint>>, 
    pub h_: Vec<Vec<RistrettoPoint>>, 
    pub l1: usize, 
    pub l2: usize 
}
 
// Definition of the structure for the commitment:
#[derive(Clone, Debug, PartialEq)]
pub struct Commit { 
    pub pk: RistrettoPoint, 
    pub a1: Vec<RistrettoPoint>, 
    pub a2: Vec<RistrettoPoint>, 
    pub b0: Vec<RistrettoPoint>, 
    pub b1: Vec<RistrettoPoint>
}

// Definition of the structure for the zero-knowledge proofs "pi_{A_1}" and "pi_{A_2}":
#[derive(Debug, PartialEq)]
pub struct ZeroKnowledgeProofA {
    pub commitment0: Vec<RistrettoPoint>,
    //pub response: Scalar,
    pub commitments: Vec<RistrettoPoint>,
    pub challenges: Vec<Scalar>,
    pub responses: Vec<Scalar>
}

// Definition of the structure for the zero-knowledge proofs "pi_B":
#[derive(Debug, PartialEq)]
pub struct ZeroKnowledgeProofB {
    pub commitment0: Vec<RistrettoPoint>,
    pub commitments1: Vec<RistrettoPoint>,
    pub challenge1: Scalar,
    pub response1: Scalar,
    pub commitments2: Vec<RistrettoPoint>,
    pub challenge2: Scalar,
    pub response2: Scalar
}

// Definition of the structure for the zero-knowledge proofs in the algorithm "Commit":
#[derive(Debug, PartialEq)]
pub struct ZeroKnowledgeProofCommit {
    pub proofa1: Vec<ZeroKnowledgeProofA>,
    pub proofa2: Vec<ZeroKnowledgeProofA>,
    pub proofb: Vec<ZeroKnowledgeProofB>
}

// Definition of the structure for the zero-knowledge proofs in the algorithm "Open":
#[derive(Debug, PartialEq)]
pub struct ZeroKnowledgeProofOpen {
    pub commitments: Vec<RistrettoPoint>,
    pub response: Scalar
}

// Definition of the structure for the zero-knowledge proofs in the algorithm "OpenLDP":
#[derive(Debug, PartialEq)]
pub struct ZeroKnowledgeProofOpenLDP {
    pub commitments0: Vec<RistrettoPoint>,
    pub challenge0: Scalar,
    pub response0: Scalar,
    pub commitments1: Vec<RistrettoPoint>,
    pub challenge1: Scalar,
    pub responses1: Vec<Scalar>
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

// Compute the sum of Scalar element:
fn sum_scalar(s: Vec<Scalar>) -> Scalar {	
    let mut sum = convert_scalar([0u8; 32]);
    for i in 0..s.len() {
    	sum = sum + s[i];  
    }
    return sum;
}

// Compute the sum of RistrettoPoint:
fn sum_ristretto(r: Vec<RistrettoPoint>) -> RistrettoPoint {
    let mut sum = RistrettoPoint::identity();
    for i in 0..r.len() {
    	sum = sum + r[i];  
    }
    return sum;
}

// Convert a [u8; 32] in Scalar:
fn convert_scalar(a: [u8; 32]) -> Scalar {   
    let s = Scalar::from_bytes_mod_order(a);
    return s
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

// Hash a vector of bytes:
pub fn hash(digest: Vec<[u8;32]>) -> Scalar {

    let mut hasher = <Sha512 as Digest>::new();

    for d in digest {
        hasher.update(d.as_slice());
    }

    let result = hasher.finalize();
    Scalar::from_bytes_mod_order_wide(&result.into())
}

// Zero-Knowledge Proofs for the Commitment:

// Proof for "pi_A".
pub fn prove_pi_a<T: CryptoRng + RngCore>(rng: &mut T, gen: RistrettoPoint, pk: RistrettoPoint, g: Vec<RistrettoPoint>, y: Vec<RistrettoPoint>, sk: Scalar, trueinstance: usize) -> ZeroKnowledgeProofA {  
    let mut random = rand_scalar(rng);  
    let mut com_0: Vec<RistrettoPoint> = Vec::new();
    let mut vec_com: Vec<RistrettoPoint> = Vec::new();
    let mut vec_chal: Vec<Scalar> = Vec::new();
    let mut vec_resp: Vec<Scalar> = Vec::new();

    // Commitment for pk:             
    let mut i = 0;
    while i < 2 {
    	if i != trueinstance {
    	    vec_chal.push(rand_scalar(rng));
    	    vec_resp.push(rand_scalar(rng));
    	    com_0.push(vec_resp[i] * gen - vec_chal[i] * pk);
    	    vec_com.push(vec_resp[i] * g[i] - vec_chal[i] * y[i]);
    	}
    	else {
    	     vec_chal.push(Scalar::from(0u32));
             vec_resp.push(Scalar::from(0u32));
             com_0.push(random * gen);
             vec_com.push(random * g[trueinstance]);       
    	}
    	i = i+1;
    }
    
    // Challenge of the proof:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    prehash.push(*(gen.compress()).as_bytes());
    for i in 0..2 {
        prehash.push(*(g[i].compress()).as_bytes());
    } 
    prehash.push(*(pk.compress()).as_bytes());
    for i in 0..2 {
        prehash.push(*(y[i].compress()).as_bytes());
    } 
    for i in 0..2 {
        prehash.push(*(com_0[i].compress()).as_bytes());
    }
    for i in 0..2 {  
    	prehash.push(*(vec_com[i].compress()).as_bytes());  
    }
    
    let chal_0 = hash(prehash);
            
    // Challenges for the verified instance:
    vec_chal[trueinstance] = chal_0 - sum_scalar((vec_chal).to_vec());
            
    // Responses for the verified instance:
    vec_resp[trueinstance] = random + sk * vec_chal[trueinstance];
    
    // Response for the instance "pk = x * gen".
    //let resp_0 = random_0 + sk * chal_0;

    //random_0.zeroize();
    random.zeroize();
            
    return ZeroKnowledgeProofA{ commitment0: com_0, commitments: vec_com, challenges: vec_chal, responses: vec_resp };
}

// Verification of the Zero-Knowledge Proof "pi_A":
pub fn verify_pi_a(gen: RistrettoPoint, pk: RistrettoPoint, g: Vec<RistrettoPoint>, y: Vec<RistrettoPoint>, proof_a: ZeroKnowledgeProofA) -> bool {
    
    //Parse proof_a:
    let com_0 = proof_a.commitment0;
    let vec_com = proof_a.commitments;
    let vec_chal = proof_a.challenges;
    let vec_resp = proof_a.responses;
    
    // Challenge of the proof:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    prehash.push(*(gen.compress()).as_bytes());
    for i in 0..2 {
        prehash.push(*(g[i].compress()).as_bytes());
    } 
    prehash.push(*(pk.compress()).as_bytes());
    for i in 0..2 {
        prehash.push(*(y[i].compress()).as_bytes());
    } 
    for i in 0..2 {
        prehash.push(*(com_0[i].compress()).as_bytes());
    }
    for i in 0..2 {  
    	prehash.push(*(vec_com[i].compress()).as_bytes());  
    }
    
    let chal_0 = hash(prehash);
	
    // Test:
    if chal_0 == sum_scalar((vec_chal).to_vec()) && vec_resp[0] * gen == com_0[0] + vec_chal[0] * pk && vec_resp[1] * gen == com_0[1] + vec_chal[1] * pk{
        for i in 0..2 {
            if vec_resp[i] * g[i] != vec_com[i] + vec_chal[i] * y[i] {
                return false;
            }
        } 
    }
    else {
        return false;
    }
    return true;
}

pub fn prove_pi_b<T: CryptoRng + RngCore>(rng: &mut T, gen: RistrettoPoint, pk: RistrettoPoint, g1: Vec<RistrettoPoint>, g2: Vec<RistrettoPoint>, y1: Vec<RistrettoPoint>, y2: Vec<RistrettoPoint>, sk: Scalar, trueinstance: usize) -> ZeroKnowledgeProofB { 
    
    if trueinstance == 1 { // The first part of instance is the verified instance.     
        // Commitment for the instance "pk = x * gen":
        let mut com_0: Vec<RistrettoPoint> = Vec::new();   
        
        // Commitment for the verified instance:
        let mut random = rand_scalar(rng);
        let mut vec_com_1: Vec<RistrettoPoint> = Vec::new();
        for i in 0..2 {
       	    vec_com_1.push(random * g1[i]);
        }
        com_0.push(random * gen);
          
        // Challenge for the unverified instance:
        let chal_2 = rand_scalar(rng); 
        
        // Response for the unverified instance:
        let resp_2 = rand_scalar(rng);
        
	// Commitment for the unverified instance:
        let mut vec_com_2: Vec<RistrettoPoint> = Vec::new();
        for i in 0..2 {
       	    vec_com_2.push(resp_2 * g2[i] - chal_2 * y2[i]);
        }
        // Simulation for the instance "pk = x * gen":
        com_0.push(resp_2 * gen - chal_2 * pk);

        // Challenge of the proof:
        let mut prehash: Vec<[u8;32]> = Vec::new();
        prehash.push(*(gen.compress()).as_bytes());
   	for i in 0..2 {
	    prehash.push(*(g1[i].compress()).as_bytes());
        }
        for i in 0..2 {
	    prehash.push(*(g2[i].compress()).as_bytes());
        }
        prehash.push(*(pk.compress()).as_bytes());
        for i in 0..2 {
	    prehash.push(*(y1[i].compress()).as_bytes());
        }
        for i in 0..2 {
	    prehash.push(*(y2[i].compress()).as_bytes());
        }
        for i in 0..2 {
            prehash.push(*(com_0[i].compress()).as_bytes());
        }
        for i in 0..2 {
            prehash.push(*(vec_com_1[i].compress()).as_bytes());
        }
        for i in 0..2 {
	    prehash.push(*(vec_com_2[i].compress()).as_bytes());
        }
        let chal_0 = hash(prehash);
        
        // Challenge for the verified instance:
        let chal_1 = chal_0 - chal_2;
        
        // Response for the verified instance:
        let resp_1 = random + sk * chal_1;
        
        random.zeroize();
        
        return ZeroKnowledgeProofB{ commitment0: com_0, commitments1: vec_com_1, challenge1: chal_1, response1: resp_1, commitments2: vec_com_2, challenge2: chal_2, response2: resp_2 };
    } 
    else { 
        let mut com_0: Vec<RistrettoPoint> = Vec::new();   
       
        // Commitment for the verified instance:
        let mut random = rand_scalar(rng);  
        let mut vec_com_2: Vec<RistrettoPoint> = Vec::new();
        for i in 0..g2.len() {
            vec_com_2.push(random * g2[i]);
        }
       
        // Challenge for the unverified instance:
        let chal_1 = rand_scalar(rng); 
        
        // Response for the unverified instance:
        let resp_1 = rand_scalar(rng);
        
        // Commitment for the unverified instance:
	let mut vec_com_1: Vec<RistrettoPoint> = Vec::new();
        for i in 0..2 {
       	    vec_com_1.push(resp_1 * g1[i] - chal_1 * y1[i]); 
        }
        // Simulation for the instance "pk = x * gen":  
        com_0.push(resp_1 * gen - chal_1 * pk);
        // Commitment for the instance "pk = x * gen":
        com_0.push(random * gen);

        // Challenge of the proof:
        let mut prehash: Vec<[u8;32]> = Vec::new();
        prehash.push(*(gen.compress()).as_bytes());
   	for i in 0..2 {
	    prehash.push(*(g1[i].compress()).as_bytes());
        }
        for i in 0..2 {
	    prehash.push(*(g2[i].compress()).as_bytes());
        }
        prehash.push(*(pk.compress()).as_bytes());
        for i in 0..2 {
	    prehash.push(*(y1[i].compress()).as_bytes());
        }
        for i in 0..2 {
	    prehash.push(*(y2[i].compress()).as_bytes());
        }
        for i in 0..2 {
            prehash.push(*(com_0[i].compress()).as_bytes());
        }
        for i in 0..2 {
            prehash.push(*(vec_com_1[i].compress()).as_bytes());
        }
        for i in 0..2 {
	    prehash.push(*(vec_com_2[i].compress()).as_bytes());
        }
        let chal_0 = hash(prehash);
        
        // Challenge for the verified instance:
        let chal_2 = chal_0 - chal_1;
        
        // Response for the verified instance:
        let resp_2 = random + sk * chal_2;
 		
 	random.zeroize();
        
        return ZeroKnowledgeProofB{ commitment0: com_0, commitments1: vec_com_1, challenge1: chal_1, response1: resp_1, commitments2: vec_com_2, challenge2: chal_2, response2: resp_2 };
    }     
}

//Verification of the Zero-Knowledge Proof "pi_B":
pub fn verify_pi_b(gen: RistrettoPoint, pk: RistrettoPoint, g1: Vec<RistrettoPoint>, g2: Vec<RistrettoPoint>, y1: Vec<RistrettoPoint>, y2: Vec<RistrettoPoint>, proof_b: ZeroKnowledgeProofB) -> bool {
    
    //Parse proof_b:
    let com_0 = proof_b.commitment0;
    let vec_com_1 = proof_b.commitments1;
    let chal_1 = proof_b.challenge1;
    let resp_1 = proof_b.response1;
    let vec_com_2 = proof_b.commitments2;
    let chal_2 = proof_b.challenge2;
    let resp_2 = proof_b.response2;
    
    // Challenge of the proof:
    let mut prehash: Vec<[u8;32]> = Vec::new();
    prehash.push(*(gen.compress()).as_bytes());
    for i in 0..2 {
	prehash.push(*(g1[i].compress()).as_bytes());
    }
    for i in 0..2 {
	prehash.push(*(g2[i].compress()).as_bytes());
    }
    prehash.push(*(pk.compress()).as_bytes());
    for i in 0..2 {
	prehash.push(*(y1[i].compress()).as_bytes());
    }
    for i in 0..2 {
	prehash.push(*(y2[i].compress()).as_bytes());
    }
    for i in 0..2 {
        prehash.push(*(com_0[i].compress()).as_bytes());
    }
    for i in 0..2 {
        prehash.push(*(vec_com_1[i].compress()).as_bytes());
    }
    for i in 0..2 {
	prehash.push(*(vec_com_2[i].compress()).as_bytes());
    }
    let chal_0 = hash(prehash);
   
    // Test:
    if chal_0 == sum_scalar(vec![chal_1, chal_2]) && resp_1 * gen == com_0[0] + chal_1 * pk && resp_2 * gen == com_0[1] + chal_2 * pk {
        for i in 0..2 {
            if resp_1 * g1[i] == vec_com_1[i] + chal_1 * y1[i] {
                if  resp_2 * g2[i] != vec_com_2[i] + chal_2 * y2[i] {
                    return false;
                }
            }
        }
    }
    else {
        return false;
    }
    return true;
}

// Zero-Knowledge Proof for Open:
pub fn prove_open<T: CryptoRng + RngCore>(rng: &mut T, gen: RistrettoPoint, g: RistrettoPoint, pk: RistrettoPoint, y: RistrettoPoint, sk: Scalar) -> ZeroKnowledgeProofOpen { 
    
    // Commitment for the instance "AND":
    let mut random = rand_scalar(rng);
    let com_0 = random * gen; 
    let com = random * g;
	
    // Challenge of the proof:  	
    let chal = hash(vec![*(gen.compress()).as_bytes(), *(g.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y.compress()).as_bytes(), *(com_0.compress()).as_bytes(), *(com.compress()).as_bytes()]);
    
    // Response for the instance "AND":
    let resp = random + sk * chal;
    
    random.zeroize();

    return ZeroKnowledgeProofOpen { commitments: vec![com_0, com], response: resp };  
}

// Verification of the proof Zero-Knowledge Proof Open:
pub fn verify_open(gen: RistrettoPoint, g: RistrettoPoint, pk: RistrettoPoint, y: RistrettoPoint, proof_open: ZeroKnowledgeProofOpen) -> bool {
	
    // Parse the proof:
    let com_0 = proof_open.commitments[0];
    let com = proof_open.commitments[1];
    let resp = proof_open.response;

    // Challenge of proof: 
    let chal = hash(vec![*(gen.compress()).as_bytes(), *(g.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y.compress()).as_bytes(), *(com_0.compress()).as_bytes(), *(com.compress()).as_bytes()]);
	
    // Test:
    if resp * gen - chal * pk != com_0 || resp * g - chal * y != com {
	    return false;
    }
    return true;
}
	
// Zero-Knowledge Proof for OpenLDP:
fn prove_openldp<T: CryptoRng + RngCore>(rng: &mut T, gen: RistrettoPoint, pk: RistrettoPoint, g1: RistrettoPoint, y1: RistrettoPoint, g2: RistrettoPoint, y2: RistrettoPoint, g3: RistrettoPoint, y3: RistrettoPoint, sk: Scalar, trueinstance: usize) -> (Vec<RistrettoPoint>, Vec<RistrettoPoint>, ZeroKnowledgeProofOpenLDP) { 
    
    if trueinstance == 0 {
    
        // Commitment for the verified instance:
        let mut random_0 = rand_scalar(rng);
        let com_00 = random_0 * gen;
        let com_01 = random_0 * g1;
        let com_02 = random_0 * g2;
        
        // Simulation of the unverified instance with "neq":
        let h = RistrettoPoint::identity() - pk;
        let h1 = RistrettoPoint::identity() - y1;
        let h3 = RistrettoPoint::identity() - y3;
        
        let y_p = RistrettoPoint::identity();
        let y3_p = RistrettoPoint::identity();
        let mut y1_p = rand_element(rng);
        while y1_p == RistrettoPoint::identity() {
            y1_p = rand_element(rng);
        }   
       
        // Challenge for the unverified instance:
        let chal_1 = rand_scalar(rng);
        
        // Responses for the unverified instance:
        let resp_u = rand_scalar(rng);
        let resp_v = rand_scalar(rng);
        
        // Commitment for the unverified instance:
        let s_0 = rand_element(rng);
        let s_1 = rand_element(rng);
        let s_3 = rand_element(rng);
        
        let r_0 = resp_u * gen + resp_v * h - s_0 - chal_1 * y_p;
        let r_1 = resp_u * g1 + resp_v * h1 - s_1 - chal_1 * y1_p;
        let r_3 = resp_u * g3 + resp_v * h3 - s_3 - chal_1 * y3_p;
		
	// Challenge of the proof:	
	let chal = hash(vec![*(gen.compress()).as_bytes(), *(g1.compress()).as_bytes(), *(g2.compress()).as_bytes(), *(g3.compress()).as_bytes(), *(h.compress()).as_bytes(), *(h1.compress()).as_bytes(), *(h3.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y1.compress()).as_bytes(), *(y2.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y1.compress()).as_bytes(), *(y3.compress()).as_bytes(), *(y_p.compress()).as_bytes(), *(y1_p.compress()).as_bytes(), *(y3_p.compress()).as_bytes(), *(com_00.compress()).as_bytes(), *(com_01.compress()).as_bytes(), *(com_02.compress()).as_bytes(), *(r_0.compress()).as_bytes(), *(r_1.compress()).as_bytes(), *(r_3.compress()).as_bytes(), *(s_0.compress()).as_bytes(), *(s_1.compress()).as_bytes(), *(s_3.compress()).as_bytes()]);
		     
        // Challenge for the true party of instance:
        let chal_0 = chal - chal_1;
        
        // Response for the true party of instance:
        let resp_0 = random_0 + chal_0 * sk;
        
        random_0.zeroize();
        
 	return (vec![h, h1, h3], vec![y_p, y1_p, y3_p], ZeroKnowledgeProofOpenLDP { commitments0: vec![com_00, com_01, com_02], challenge0: chal_0, response0: resp_0, commitments1: vec![r_0, r_1, r_3, s_0, s_1, s_3], challenge1: chal_1, responses1: vec![resp_u, resp_v] });				
    }    
    else {
    	
    	let mut random = rand_scalar(rng);
    	
        // Instance with "non equality of discret log":
        let b = random;
        let a = sk * random;
        
        let h = RistrettoPoint::identity() - pk;
        let h1 = RistrettoPoint::identity() - y1;
        let h3 = RistrettoPoint::identity() - y3; 
        
        let y_p = a * gen + b * h;
        let y1_p = a * g1 + b * h1;
        let y3_p = a * g3 + b * h3;
     
       	// Commitment for the true party of instance:
        let mut random_r = rand_scalar(rng);
        let mut random_s = rand_scalar(rng);
        
        let r_0 = random_r * gen;
        let s_0 = random_s * h;
        let r_1 = random_r * g1;
        let s_1 = random_s * h1;
        let r_3 = random_r * g3;
        let s_3 = random_s * h3;
        
        // Simulation of the instance:  
        // Challenge:
        let chal_0 = rand_scalar(rng);
        
        // Response:
        let resp_0 = rand_scalar(rng);
        
    	// Commitment:
    	let com_00 = resp_0 * gen - chal_0 * pk;
        let com_01 = resp_0 * g1 - chal_0 * y1;
        let com_02 = resp_0 * g2 - chal_0 * y2;
        
        // Challenge of the proof:
	let chal = hash(vec![*(gen.compress()).as_bytes(), *(g1.compress()).as_bytes(), *(g2.compress()).as_bytes(), *(g3.compress()).as_bytes(), *(h.compress()).as_bytes(), *(h1.compress()).as_bytes(), *(h3.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y1.compress()).as_bytes(), *(y2.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y1.compress()).as_bytes(), *(y3.compress()).as_bytes(), *(y_p.compress()).as_bytes(), *(y1_p.compress()).as_bytes(), *(y3_p.compress()).as_bytes(), *(com_00.compress()).as_bytes(), *(com_01.compress()).as_bytes(), *(com_02.compress()).as_bytes(), *(r_0.compress()).as_bytes(), *(r_1.compress()).as_bytes(), *(r_3.compress()).as_bytes(), *(s_0.compress()).as_bytes(), *(s_1.compress()).as_bytes(), *(s_3.compress()).as_bytes()]);
        
        // Challenge for the true party of instance:
        let chal_1 = chal - chal_0;
        
        // Response for the true party of instance:
        let resp_u = random_r + chal_1 * a;
        let resp_v = random_s + chal_1 * b;
        
        random.zeroize();
        random_r.zeroize();
        random_s.zeroize();
        
        return (vec![h, h1, h3], vec![y_p, y1_p, y3_p], ZeroKnowledgeProofOpenLDP { commitments0: vec![com_00, com_01, com_02], challenge0: chal_0, response0: resp_0, commitments1: vec![r_0, r_1, r_3, s_0, s_1, s_3], challenge1: chal_1, responses1: vec![resp_u, resp_v] });
    } 
}

// Verification of the proof Zero-Knowledge Proof Openldp:
fn verify_openldp(gen: RistrettoPoint, pk: RistrettoPoint, g1: RistrettoPoint, y1: RistrettoPoint, g2: RistrettoPoint, y2: RistrettoPoint, g3: RistrettoPoint, y3: RistrettoPoint, h: RistrettoPoint, h1: RistrettoPoint, h3: RistrettoPoint, y_p: RistrettoPoint, y1_p: RistrettoPoint, y3_p: RistrettoPoint, proof_openldp: ZeroKnowledgeProofOpenLDP) -> bool {

    // Parse the proof:
    let com_00 = proof_openldp.commitments0[0];
    let com_01 = proof_openldp.commitments0[1];
    let com_02 = proof_openldp.commitments0[2];
    let chal_0 = proof_openldp.challenge0;
    let resp_0 = proof_openldp.response0;
    let r_0 = proof_openldp.commitments1[0];
    let r_1 = proof_openldp.commitments1[1];
    let r_3 = proof_openldp.commitments1[2];
    let s_0 = proof_openldp.commitments1[3];
    let s_1 = proof_openldp.commitments1[4];
    let s_3 = proof_openldp.commitments1[5];
    let chal_1 = proof_openldp.challenge1;
    let resp_u = (proof_openldp.responses1)[0];
    let resp_v = (proof_openldp.responses1)[1];   
    
    // Challenge of the proof:  	
    let chal = hash(vec![*(gen.compress()).as_bytes(), *(g1.compress()).as_bytes(), *(g2.compress()).as_bytes(), *(g3.compress()).as_bytes(), *(h.compress()).as_bytes(), *(h1.compress()).as_bytes(), *(h3.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y1.compress()).as_bytes(), *(y2.compress()).as_bytes(), *(pk.compress()).as_bytes(), *(y1.compress()).as_bytes(), *(y3.compress()).as_bytes(), *(y_p.compress()).as_bytes(), *(y1_p.compress()).as_bytes(), *(y3_p.compress()).as_bytes(), *(com_00.compress()).as_bytes(), *(com_01.compress()).as_bytes(), *(com_02.compress()).as_bytes(), *(r_0.compress()).as_bytes(), *(r_1.compress()).as_bytes(), *(r_3.compress()).as_bytes(), *(s_0.compress()).as_bytes(), *(s_1.compress()).as_bytes(), *(s_3.compress()).as_bytes()]);

    // Test:
    if chal == chal_0 + chal_1 && y_p == RistrettoPoint::identity() && y1_p != RistrettoPoint::identity() && y3_p == RistrettoPoint::identity() {
	    if com_00 != resp_0 * gen - chal_0 * pk || com_01 != resp_0 * g1 - chal_0 * y1 || com_02 != resp_0 * g2 - chal_0 * y2 {
	        return false;
	    }
	    if r_0 != resp_u * gen + resp_v * h - s_0 - chal_1 * y_p || r_1 != resp_u * g1 + resp_v * h1 - s_1 - chal_1 * y1_p || r_3 != resp_u * g3 + resp_v * h3 - s_3 - chal_1 * y3_p {
	        return false;
	    }
    }
    else {
	    return false;
    }
    return true;
}

// Generate a setup set:
pub fn setup<T: CryptoRng + RngCore>(rng: &mut T, l_1: usize, l_2: usize) -> Set {
    
    let mut g_0: Vec<RistrettoPoint> = Vec::new();
    let mut g_1: Vec<RistrettoPoint> = Vec::new();
    let mut f_0: Vec<RistrettoPoint> = Vec::new();
    let mut f_1: Vec<RistrettoPoint> = Vec::new();
    let mut h_0: Vec<RistrettoPoint> = Vec::new();
    let mut h_1: Vec<RistrettoPoint> = Vec::new();
    for _i in 0..l_1 {
        g_0.push(rand_element(rng));
        g_1.push(rand_element(rng));
    }
    let g = vec![g_0, g_1];
    for _i in 0..l_2 {
        f_0.push(rand_element(rng));
        f_1.push(rand_element(rng));
        h_0.push(rand_element(rng));
        h_1.push(rand_element(rng));
    }
    let f = vec![f_0, f_1];
    let h = vec![h_0, h_1];
    let generator = RISTRETTO_BASEPOINT_POINT;
    let set = Set{ gen: generator, g_: g, f_: f, h_: h, l1: l_1, l2: l_2 };  
    return set;   
}

// Generate a commitment for a message m:
pub fn commit<T: CryptoRng + RngCore>(rng: &mut T, set: Set, m: Vec<usize>, theta: Vec<Vec<usize>>) -> (Scalar, Commit, ZeroKnowledgeProofCommit) {

    let x = rand_scalar(rng); // pick a random secret key.
    
    // Parse set:
    let generator = set.gen;
    let g = set.g_;
    let f = set.f_;
    let h = set.h_;
    let l_1 = set.l1;
    let l_2 = set.l2;

    // Parse theta as (s,t):
    let s = &theta[0];
    let t = &theta[1];
    
    // Compute "A_(i,1)":
    let mut vec_a1: Vec<RistrettoPoint> = Vec::new();
    for i in 0..l_1 {
    	vec_a1.push(g[s[i]][i]);
    }
     
    // Compute "A_(i,2)":
    let mut vec_a2: Vec<RistrettoPoint> = Vec::new();
    let mut vec_b0: Vec<RistrettoPoint> = Vec::new();
    let mut vec_b1: Vec<RistrettoPoint> = Vec::new();
    for i in 0..l_2 {
    	vec_a2.push(f[m[i]][i]);
    	vec_b0.push(h[t[i]][i]);
    	vec_b1.push(h[1-t[i]][i]);
    }

    let mut a_1: Vec<RistrettoPoint> = Vec::new();
    let mut a_2: Vec<RistrettoPoint> = Vec::new();
    let mut b_0: Vec<RistrettoPoint> = Vec::new();
    let mut b_1: Vec<RistrettoPoint> = Vec::new();
    
    for i in 0..l_1{
    	a_1.push(x * vec_a1[i]);
    }
    
    for i in 0..l_2{
    	a_2.push(x * vec_a2[i]);
    	b_0.push(x * vec_b0[i]);
    	b_1.push(x * vec_b1[i]);
    }
	
    let y = x * generator; 
    let c = Commit { pk: y, a1: (&a_1).to_vec(), a2: (&a_2).to_vec(), b0: (&b_0).to_vec(), b1: (&b_1).to_vec() };
    
    let mut proof_a_1: Vec<ZeroKnowledgeProofA> = Vec::new();
    let mut proof_a_2: Vec<ZeroKnowledgeProofA> = Vec::new();
    let mut proof_b: Vec<ZeroKnowledgeProofB> = Vec::new();
    
    // Zero-knowledge proof "pi_{A_1}":
    for i in 0..l_1 {
        let mut trueinstance = 0;
        if y == x * generator && a_1[i] == x * g[1][i] { // The first party of instance is true.
            trueinstance = 1;
        }
        let pi_a = prove_pi_a(rng, generator, y, vec![g[0][i], g[1][i]], vec![a_1[i], a_1[i]], x, trueinstance);
        proof_a_1.push(pi_a);
    }
    
    // Zero-knowledge proof "pi_{A_2}":
    for i in 0..l_2 {
        let mut trueinstance = 0;
        if y == x * generator && a_2[i] == x * f[1][i] { // The second party of instance is true.
            trueinstance = 1;
        }
        let pi_a = prove_pi_a(rng, generator, y, vec![f[0][i], f[1][i]], vec![a_2[i], a_2[i]], x, trueinstance);
        proof_a_2.push(pi_a);
    }
    
    // Zero-knowledge proof "pi_{B}":
    for i in 0..l_2 {
        let mut trueinstance = 2;
        if y == x * generator && b_0[i] == x * h[0][i] && b_1[i] == x * h[1][i] { // The first party of instance is true.
            trueinstance = 1;
        }
        let pi_b = prove_pi_b(rng, generator, y, vec![h[0][i], h[1][i]], vec![h[1][i], h[0][i]], vec![b_0[i], b_1[i]],vec![b_0[i], b_1[i]], x, trueinstance);
        proof_b.push(pi_b);        
    } 
    let proof_comm = ZeroKnowledgeProofCommit{ proofa1: proof_a_1, proofa2: proof_a_2, proofb: proof_b } ;
       
    return (x, c, proof_comm);
}

// Verify the proof of commitment:
pub fn ver_commit(set: Set, c: Commit, proof_comm: ZeroKnowledgeProofCommit) -> bool { 

    // Parse set:
    let generator = set.gen;
    let g = set.g_;
    let f = set.f_;
    let h = set.h_;
    let l_1 = set.l1;
    let l_2 = set.l2;
    
    // Parse c:
    let y = c.pk;
    let a_1 = c.a1;
    let a_2 = c.a2;
    let b_0 = c.b0;
    let b_1 = c.b1;
    
    // Parse proof_comm:
    let proof_a_1 = proof_comm.proofa1;
    let proof_a_2 = proof_comm.proofa2;
    let proof_b = proof_comm.proofb; 
    
    for i in 0..l_1 {
        let p = ZeroKnowledgeProofA{ commitment0: (&proof_a_1[i].commitment0).to_vec(), commitments: (&proof_a_1[i].commitments).to_vec(), challenges: (&proof_a_1[i].challenges).to_vec(), responses: (&proof_a_1[i].responses).to_vec() };
        if verify_pi_a(generator, y, vec![g[0][i], g[1][i]], vec![a_1[i], a_1[i]], p) == false {
            return false;
        }
    }
    
    for i in 0..l_2 {
        let p = ZeroKnowledgeProofA{ commitment0: (&proof_a_2[i].commitment0).to_vec(), commitments: (&proof_a_2[i].commitments).to_vec(), challenges: (&proof_a_2[i].challenges).to_vec(), responses: (&proof_a_2[i].responses).to_vec() };
        if verify_pi_a(generator, y, vec![f[0][i], f[1][i]], vec![a_2[i], a_2[i]], p) == false {
            return false;
        }
    }
    
    for i in 0..l_2 {
        let p = ZeroKnowledgeProofB{ commitment0: (&proof_b[i].commitment0).to_vec(), commitments1: (&proof_b[i].commitments1).to_vec(), challenge1: proof_b[i].challenge1, response1: proof_b[i].response1, commitments2: (&proof_b[i].commitments2).to_vec(), challenge2: proof_b[i].challenge2, response2: proof_b[i].response2 };
        if verify_pi_b(generator, y, vec![h[0][i], h[1][i]], vec![h[1][i], h[0][i]], vec![b_0[i], b_1[i]], vec![b_0[i], b_1[i]], p) == false {      
            return false;
        }
    }
    return true;   
}

// Open the commitment:
pub fn open<T: CryptoRng + RngCore>(rng: &mut T, set: Set, k: Scalar, c: Commit) -> (Vec<usize>, ZeroKnowledgeProofOpen) {
	
    // Parse set:
    let generator = set.gen;
    let f = set.f_;
    let l_2 = set.l2;
	
    // Parse k:
    let x = k;
	
    // Parse c:
    let y = c.pk;
    let a_2 = c.a2;
		
    let mut alpha_2: Vec<RistrettoPoint> = Vec::new();
    let mut m: Vec<usize> = Vec::new();
    for i in 0..l_2 {
        if a_2[i] == x * f[0][i] {	
	    m.push(0);
            alpha_2.push(f[0][i]);
	}
	if a_2[i] == x * f[1][i] {
	    m.push(1);
	    alpha_2.push(f[1][i]);
	}
    }
    let prod_a_2 = sum_ristretto((&a_2).to_vec());
    let prod_alpha_2 = sum_ristretto((&alpha_2).to_vec());
    let proof_open = prove_open(rng, generator, prod_alpha_2, y, prod_a_2, x);
	
    return (m, proof_open);
}

// Verify the opening:
pub fn ver_open(set: Set, c: Commit, m: Vec<usize>, proof_open: ZeroKnowledgeProofOpen) -> bool {

    // Parse set:
    let generator = set.gen;
    let f = set.f_;
    let l_2 = set.l2;
	
    // Parse c:
    let y = c.pk;
    let a_2 = c.a2;
	
    let mut alpha_2: Vec<RistrettoPoint> = Vec::new();
	
    for i in 0..l_2 {
	    alpha_2.push(f[m[i]][i]);	
    }
	
    let prod_a_2 = sum_ristretto((&a_2).to_vec());
    let prod_alpha_2 = sum_ristretto((&alpha_2).to_vec());

    return verify_open(generator, prod_alpha_2, y, prod_a_2, proof_open); 	
}

// Open the commitment with LDP:
pub fn openldp<T: CryptoRng + RngCore>(rng: &mut T, set: Set, k: Scalar, c: Commit, hat_theta: Vec<Vec<usize>>) -> (Vec<usize>, Vec<RistrettoPoint>, Vec<RistrettoPoint>, ZeroKnowledgeProofOpenLDP){
	
    // Parse set:
    let generator = set.gen;
    let g = set.g_;
    let f = set.f_;
    let h = set.h_;
    let l_1 = set.l1;
    let l_2 = set.l2;
	
    // Parse k:
    let x = k;
	
    // Parse c:
    let y = c.pk;
    let a_1 = c.a1;
    let a_2 = c.a2;
    let b_0 = c.b0;
    let b_1 = c.b1;
    
    // Parse hat theta:
    let hat_s = &hat_theta[0];
    let hat_t = &hat_theta[1];
    
    let mut prod_a_1 = RistrettoPoint::identity();
    let mut prod_alpha_1 = RistrettoPoint::identity();
    let mut prod_a_2 = RistrettoPoint::identity();
    let mut prod_alpha_2 = RistrettoPoint::identity();
    let mut prod_beta = RistrettoPoint::identity();
    let mut prod_gamma = RistrettoPoint::identity();
    let mut hat_m: Vec<usize> = Vec::new();
    let mut m: Vec<usize> = Vec::new();
    let mut trueinstance = 0;
    
    for i in 0..l_1 {
        prod_a_1 = prod_a_1 + a_1[i];
        prod_alpha_1 += g[hat_s[i]][i];
    }
	
    if prod_a_1 == &x * prod_alpha_1 {
	    for i in 0..l_2 {
    	    prod_a_2 = prod_a_2 + a_2[i];
    	    if a_2[i] == x * f[0][i] { // m[i] == 0 
    		    m.push(0);
    		    prod_alpha_2 = prod_alpha_2 + f[0][i];
		        prod_beta = prod_beta + b_0[i];
	        }
	        if a_2[i] == x * f[1][i] { // m[i] == 1
		        m.push(1);
		        prod_alpha_2 = prod_alpha_2 + f[1][i];
		        prod_beta = prod_beta + b_1[i];
	        }
	        if hat_t[i] == 0 {
		        prod_gamma = prod_gamma + h[0][i];
	        }
	        if hat_t[i] == 1 {
		        prod_gamma = prod_gamma + h[1][i];
	        }
	    }
	    hat_m = m;
    }
	
    if prod_a_1 != x * prod_alpha_1 {
	    trueinstance = 1;
	    for i in 0..l_2 {
	        prod_a_2 = prod_a_2 + a_2[i];
	        if hat_t[i] == 0 {
		        prod_gamma = prod_gamma + h[0][i];
	            if b_0[i] == x*h[0][i] { // t[i] = 0
		            hat_m.push(0); 
		            prod_alpha_2 = prod_alpha_2 + f[0][i];
		            prod_beta = prod_beta + b_0[i];	
		        }
		        else { // t[i] = 1
		            hat_m.push(1);
		            prod_alpha_2 = prod_alpha_2 + f[1][i]; 
		            prod_beta = prod_beta + b_1[i];	
		        }
	        }
	        else { // hat_t[i] == 1
		        prod_gamma = prod_gamma + h[1][i];
		        if b_0[i] == x * h[0][i] { // t[i] = 0
		            hat_m.push(1);
		            prod_alpha_2 = prod_alpha_2 + f[1][i];
		            prod_beta = prod_beta + b_1[i];
		        }
		        else {
		            hat_m.push(0);
		            prod_alpha_2 = prod_alpha_2 + f[0][i];
		            prod_beta = prod_beta + b_0[i];	
		        }			
	        }
	    }
    }
	
    let resp_openldp = prove_openldp(rng, generator, y, prod_alpha_1, prod_a_1, prod_alpha_2, prod_a_2, prod_gamma, prod_beta, x, trueinstance);
    let vec_h = resp_openldp.0;
    let vec_y_p = vec![(resp_openldp.1)[0], (resp_openldp.1)[1], (resp_openldp.1)[2]] ; 
    let proof_openldp = resp_openldp.2;
	
    return (hat_m, vec_h, vec_y_p, proof_openldp);	
}	

// Verify the opening with LDP:
pub fn ver_openldp(set: Set, c: Commit, hat_m: Vec<usize>, vec_h: Vec<RistrettoPoint>, vec_y_p: Vec<RistrettoPoint>, proof_openldp: ZeroKnowledgeProofOpenLDP, hat_theta: Vec<Vec<usize>>) -> bool {

    // Parse set:
    let generator = set.gen;
    let g = set.g_;
    let f = set.f_;
    let h = set.h_;
    let l_1 = set.l1;
    let l_2 = set.l2;
	
    // Parse c:
    let y = c.pk;
    let a_1 = c.a1;
    let a_2 = c.a2;
    let b_0 = c.b0;
    let b_1 = c.b1;
    
    // Parse vec_h:
    let h0 = vec_h[0];
    let h1 = vec_h[1];
    let h3 = vec_h[2];
    
    // Parse vec_y_p:
    let y0_p = vec_y_p[0];
    let y1_p = vec_y_p[1];
    let y3_p = vec_y_p[2];
    
    // Parse hat theta:
    let hat_s = &hat_theta[0];
    let hat_t = &hat_theta[1];
    
    let mut prod_a_1 = RistrettoPoint::identity();
    let mut prod_alpha_1 = RistrettoPoint::identity();
	
    for i in 0..l_1 {
	    prod_a_1 = prod_a_1 + a_1[i];
	    prod_alpha_1  = prod_alpha_1 + g[hat_s[i]][i];
    }
	
    let mut prod_a_2 = RistrettoPoint::identity();
    let mut prod_alpha_2 = RistrettoPoint::identity();
    let mut prod_beta = RistrettoPoint::identity();
    let mut prod_gamma = RistrettoPoint::identity();

    for i in 0..l_2 {
	prod_a_2 = prod_a_2 + a_2[i];
	prod_alpha_2 = prod_alpha_2 + f[hat_m[i]][i];
	if hat_m[i] == 0 {
	    prod_beta = prod_beta + b_0[i]; 
	}
	if hat_m[i] == 1 {
	    prod_beta = prod_beta + b_1[i];
	}
	prod_gamma = prod_gamma + h[hat_t[i]][i];
    }
 	
    return verify_openldp(generator, y, prod_alpha_1, prod_a_1, prod_alpha_2, prod_a_2, prod_gamma, prod_beta, h0, h1, h3, y0_p, y1_p, y3_p, proof_openldp); 
}

// Generate a public/ secret key:
pub fn gen<T: CryptoRng + RngCore>(rng: &mut T, g: RistrettoPoint) -> (Scalar, RistrettoPoint) {
    let secret_key = rand_scalar(rng);
    let public_key = secret_key * g;
    return (secret_key, public_key);
}

// Generate a signature of Commitment:
pub fn sign<T: CryptoRng + RngCore>(rng: &mut T, c: Commit, g: RistrettoPoint, pubk: RistrettoPoint, secretk: Scalar) -> Signature {

    let mut rand = rand_scalar(rng);
    let r_ = rand * g;
	
    // Challenge:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    prehash.push(*(g.compress()).as_bytes());
    prehash.push(*(pubk.compress()).as_bytes());
    prehash.push(*(r_.compress()).as_bytes());
    prehash.push(*(c.pk.compress()).as_bytes());
    for i in 0..c.a1.len() {
    	prehash.push(*(c.a1[i].compress()).as_bytes());
    }
    for i in 0..c.a2.len() {
    	prehash.push(*(c.a2[i].compress()).as_bytes());
    }
    for i in 0..c.b0.len() {
    	prehash.push(*(c.b0[i].compress()).as_bytes());
    }
    for i in 0..c.b1.len() {
    	prehash.push(*(c.b1[i].compress()).as_bytes());
    }
    
    let chal = hash(prehash);
	
    // Response:
    let z_ = rand + chal * secretk;
	
    rand.zeroize();
	
    return Signature { r: r_, z: z_ };
}

// Verify the signature:
pub fn ver(c: Commit, g: RistrettoPoint, pubk: RistrettoPoint, s: Signature) -> bool {

    let r_ = s.r;
    let z_ = s.z;
	
    // Challenge:
    let mut prehash: Vec<[u8; 32]> = Vec::new();
    prehash.push(*(g.compress()).as_bytes());
    prehash.push(*(pubk.compress()).as_bytes());
    prehash.push(*(r_.compress()).as_bytes());
    prehash.push(*(c.pk.compress()).as_bytes());
    for i in 0..c.a1.len() {
    	prehash.push(*(c.a1[i].compress()).as_bytes());
    }
    for i in 0..c.a2.len() {
    	prehash.push(*(c.a2[i].compress()).as_bytes());
    }
    for i in 0..c.b0.len() {
    	prehash.push(*(c.b0[i].compress()).as_bytes());
    }
    for i in 0..c.b1.len() {
    	prehash.push(*(c.b1[i].compress()).as_bytes());
    }
    
    let chal = hash(prehash);
	
    // Test:
    if r_ == z_ * g - chal * pubk {
	return true;
    }
    return false;
}

// Write the setup in a file:
fn writesetup(set: &Set) -> io::Result<()>{
    let mut setup: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("setup.txt")?;
    match set{
    	Set{ gen, g_, f_, h_, l1, l2 } => {
    	    setup.push(((gen).compress()).to_bytes());
    	    for i in 0..2 {
    	        for j in 0..*l1 {
    	            setup.push(((g_[i][j]).compress()).to_bytes()); 
    	        }
    	    }
    	    for i in 0..2 {
    	        for j in 0..*l2 {
    	            setup.push(((f_[i][j]).compress()).to_bytes());
    	        } 
    	    }
    	    for i in 0..2 {
    	        for j in 0..*l2 {
    	            setup.push(((h_[i][j]).compress()).to_bytes());
    	        } 
    	    }
            setup.push(usize_to_u8_array(*l1));
    	    setup.push(usize_to_u8_array(*l2));
        },
    }
    for i in 0..setup.len(){
        file.write_vectored(&[IoSlice::new(&setup[i])])?;
    }
    return Ok(())
} 

// Export the setup located in a file:
fn exportsetup() -> Set{
    let mut buffer = Vec::new();
    let file = File::open("setup.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut setup: Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len() {
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0{
    		setup.push(array.clone());
    	}
    }
    let l = setup.len();
    let l_1 = u8_array_to_usize(setup[l-2]);
    let l_2 = u8_array_to_usize(setup[l-1]);
    
    let generator = CompressedRistretto(setup[0]).decompress().unwrap();
    let mut gg: Vec<Vec<RistrettoPoint>> = Vec::new();
    let mut ff: Vec<Vec<RistrettoPoint>> = Vec::new();
    let mut hh: Vec<Vec<RistrettoPoint>> = Vec::new();
    let mut compt = 1;
    let mut g0: Vec<RistrettoPoint> = Vec::new();
    for j in compt..compt + l_1 {
    	g0.push(CompressedRistretto(setup[j]).decompress().unwrap()); 
    }
    compt = compt + l_1;
    gg.push(g0);
    let mut g1: Vec<RistrettoPoint> = Vec::new();
    for j in compt..compt + l_1 {
    	g1.push(CompressedRistretto(setup[j]).decompress().unwrap()); 
    }
    compt = compt + l_1;
    gg.push(g1);
    
    let mut f0: Vec<RistrettoPoint> = Vec::new();
    for j in compt..compt + l_2 {
    	f0.push(CompressedRistretto(setup[j]).decompress().unwrap()); 
    }
    compt = compt + l_2;
    ff.push(f0);
    let mut f1: Vec<RistrettoPoint> = Vec::new();
    for j in compt..compt + l_2 {
    	f1.push(CompressedRistretto(setup[j]).decompress().unwrap()); 
    }
    compt = compt + l_2;
    ff.push(f1);
    
    let mut h0: Vec<RistrettoPoint> = Vec::new();
    for j in compt..compt + l_2 {
    	h0.push(CompressedRistretto(setup[j]).decompress().unwrap()); 
    }
    compt = compt + l_2;
    hh.push(h0);
    let mut h1: Vec<RistrettoPoint> = Vec::new();
    for j in compt..compt + l_2 {
    	h1.push(CompressedRistretto(setup[j]).decompress().unwrap()); 
    }
    hh.push(h1);
    
    return Set{ gen: generator, g_: gg, f_: ff, h_: hh, l1: l_1, l2: l_2 };
}


// Write the commitment in a file:
fn writecommit(c: &Commit) -> io::Result<()>{
    let mut com: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("commitment.txt")?;
    match c{
    	Commit{	pk, a1, a2, b0, b1 } =>{
    	    com.push(((pk).compress()).to_bytes());
    	    for i in 0..a1.len(){
    	        com.push(((a1[i]).compress()).to_bytes());		    
    	    }
    	    for i in 0..a2.len(){
    	        com.push(((a2[i]).compress()).to_bytes());		   
    	    }
    	    for i in 0..b0.len(){
    	        com.push(((b0[i]).compress()).to_bytes());		   
    	    }
    	    for i in 0..b1.len(){
    	        com.push(((b1[i]).compress()).to_bytes());		   
    	    }
        },
    }
    for i in 0..com.len(){
        file.write_vectored(&[IoSlice::new(&com[i])])?;
    }
    return Ok(())
}    
 
// Read the commitment located in a file.
fn exportcommit(l1: usize, l2: usize) -> Commit{
    let mut buffer = Vec::new();
    let file = File::open("commitment.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut com : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len(){
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0{
    		com.push(array.clone());
    	}
    }
    // pk
    let pubk = CompressedRistretto(com[0]).decompress().unwrap();
    let mut a_1: Vec<RistrettoPoint> = Vec::new();
    let mut a_2: Vec<RistrettoPoint> = Vec::new();
    let mut b_0: Vec<RistrettoPoint> = Vec::new();
    let mut b_1: Vec<RistrettoPoint> = Vec::new();
    
    // a1
    let mut compt = 1; 
    for i in compt..compt + l1{
    	a_1.push(CompressedRistretto(com[i]).decompress().unwrap());
    }
    compt = compt + l1;
    // a2
    for i in compt..compt + l2{
    	a_2.push(CompressedRistretto(com[i]).decompress().unwrap());
    }
    compt = compt + l2;
    // b0
    for i in compt..compt + l2{
    	b_0.push(CompressedRistretto(com[i]).decompress().unwrap());
    }
    compt = compt + l2;
    // b1
    for i in compt..compt + l2{
    	b_1.push(CompressedRistretto(com[i]).decompress().unwrap());
    }
    return Commit{pk: pubk, a1: a_1, a2: a_2, b0: b_0, b1: b_1};
}

// Write the proof of commitment in a file:
fn writeproofcommit(p: &ZeroKnowledgeProofCommit, l1: usize, l2: usize) -> io::Result<()>{
    let mut proof: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("proofcommitment.txt")?;
    
    match p {
    	ZeroKnowledgeProofCommit{ proofa1, proofa2, proofb } => {
	    for i in 0..l1{
    	    	match &proofa1[i] { 
    	    	    ZeroKnowledgeProofA{ commitment0, commitments, challenges, responses } => {
    	    	        for j in 0..2{
    	    	            proof.push(((commitment0[j]).compress()).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push(((commitments[j]).compress()).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push((challenges[j]).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push((responses[j]).to_bytes());
    	    	        }
    	    	    }
    	        }
    	    }
    	    for i in 0..l2{
    	    	match &proofa2[i]{ 
    	    	    ZeroKnowledgeProofA{ commitment0, commitments, challenges, responses } => {
    	    	        for j in 0..2{
    	    	            proof.push(((commitment0[j]).compress()).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push(((commitments[j]).compress()).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push((challenges[j]).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push((responses[j]).to_bytes());
    	    	        }
    	    	    }
    	        }
    	    }
    	    for i in 0..l2{
    	    	match &proofb[i]{ 
    	    	    ZeroKnowledgeProofB{ commitment0, commitments1, challenge1, response1, commitments2, challenge2, response2 } => {
    	    	      	for j in 0..2{
    	    	            proof.push(((commitment0[j]).compress()).to_bytes());
    	    	        }
    	    	        for j in 0..2{
    	    	            proof.push(((commitments1[j]).compress()).to_bytes());
    	    	        }
    	    	        proof.push((challenge1).to_bytes());
    	    	        proof.push((response1).to_bytes());
    	    	        for j in 0..2{
    	    	            proof.push(((commitments2[j]).compress()).to_bytes());
    	    	        }
    	    	        proof.push((challenge2).to_bytes());
    	    	        proof.push((response2).to_bytes());
    	    	        
    	    	    }
    	    	}
    	    }
    	}
    }	    
    for k in 0..proof.len(){
        file.write_vectored(&[IoSlice::new(&proof[k])])?;
    }
    return Ok(())
}

// Read the proof of commitment located in a file.
fn exportproofcommit(l1: usize, l2: usize) -> ZeroKnowledgeProofCommit{
    let mut buffer = Vec::new();
    let file = File::open("proofcommitment.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut p : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len(){
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0{
    		p.push(array.clone());
    	}
    }
    let mut compt = 0;
    
    // proofa1
    let mut proof_a1: Vec<ZeroKnowledgeProofA> = Vec::new();
    for _i in 0..l1{
        let mut r0: Vec<RistrettoPoint> = Vec::new();
    	let mut r: Vec<RistrettoPoint> = Vec::new();
    	let mut c: Vec<Scalar> = Vec::new();
    	let mut z: Vec<Scalar> = Vec::new();
    	
    	r0.push(CompressedRistretto(p[compt]).decompress().unwrap());
        r0.push(CompressedRistretto(p[compt + 1]).decompress().unwrap());
    	compt = compt + 2; 
    	
    	for j in compt..compt + 2{
    	    r.push(CompressedRistretto(p[j]).decompress().unwrap());
    	}
    	compt = compt + 2;
        for j in compt..compt + 2{
    	    c.push(Scalar::from_bytes_mod_order(p[j]));
    	}
    	compt = compt + 2;
        for j in compt..compt + 2{
    	    z.push(Scalar::from_bytes_mod_order(p[j]));
    	}
    	compt = compt + 2;
    	proof_a1.push(ZeroKnowledgeProofA{ commitment0: r0, commitments: r, challenges: c, responses: z});  	
    }
    
    compt = 8 * l1;
    // proofa2
    let mut proof_a2: Vec<ZeroKnowledgeProofA> = Vec::new();
    for _i in 0..l2{
        let mut r0: Vec<RistrettoPoint> = Vec::new();
    	let mut r: Vec<RistrettoPoint> = Vec::new();
    	let mut c: Vec<Scalar> = Vec::new();
    	let mut z: Vec<Scalar> = Vec::new();
    	
    	r0.push(CompressedRistretto(p[compt]).decompress().unwrap());
    	r0.push(CompressedRistretto(p[compt+1]).decompress().unwrap());
    	compt = compt + 2;
    	for j in compt..compt + 2{
    	    r.push(CompressedRistretto(p[j]).decompress().unwrap());
    	}
    	compt = compt + 2;
        for j in compt..compt + 2{
    	    c.push(Scalar::from_bytes_mod_order(p[j]));
    	}
    	compt = compt + 2;
        for j in compt..compt + 2{
    	    z.push(Scalar::from_bytes_mod_order(p[j]));
    	}
    	compt = compt + 2;
    	proof_a2.push(ZeroKnowledgeProofA{ commitment0: r0, commitments: r, challenges: c, responses: z });  	
    }
    
    compt = 8 * l1 + 8 * l2;
    
    // proofb
    let mut proof_b: Vec<ZeroKnowledgeProofB> = Vec::new();
    for _i in 0..l2{
        let mut r0: Vec<RistrettoPoint> = Vec::new();
    	let mut r1: Vec<RistrettoPoint> = Vec::new();
    	let mut r2: Vec<RistrettoPoint> = Vec::new();
    	
    	r0.push(CompressedRistretto(p[compt]).decompress().unwrap());
    	r0.push(CompressedRistretto(p[compt+1]).decompress().unwrap());
    	compt = compt + 2;
    	for j in compt..compt+2{
    	    r1.push(CompressedRistretto(p[j]).decompress().unwrap());
    	}
    	compt = compt + 2;
    	let c1 = Scalar::from_bytes_mod_order(p[compt]);
    	let z1 = Scalar::from_bytes_mod_order(p[compt + 1]);
    	compt = compt + 2;
        for j in compt..compt+2{
    	    r2.push(CompressedRistretto(p[j]).decompress().unwrap());
    	}
	compt = compt + 2;
    	let c2 = Scalar::from_bytes_mod_order(p[compt]);
    	let z2 = Scalar::from_bytes_mod_order(p[compt + 1]);
    	compt = compt + 2;
    	proof_b.push(ZeroKnowledgeProofB{ commitment0: r0, commitments1: r1, challenge1: c1, response1: z1, commitments2: r2, challenge2: c2, response2: z2 });  	
    }
    return ZeroKnowledgeProofCommit{ proofa1: proof_a1, proofa2: proof_a2, proofb: proof_b };  
} 

// Write the proof of opening in a file:
fn writeproofopen(p: &ZeroKnowledgeProofOpen) -> io::Result<()>{
    let mut proof: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("proofopening.txt")?;
    
    match p {
    	ZeroKnowledgeProofOpen{ commitments, response } => {
	    for j in 0..commitments.len(){
    	    	proof.push(((commitments[j]).compress()).to_bytes());
    	    }
    	    proof.push((response).to_bytes());
    	}
    }	    
    for k in 0..proof.len(){
        file.write_vectored(&[IoSlice::new(&proof[k])])?;
    }
    return Ok(())
} 

// Read the proof of opening located in a file.
fn exportproofopen() -> ZeroKnowledgeProofOpen{
    let mut buffer = Vec::new();
    let file = File::open("proofopening.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut p : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len(){
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0{
    		p.push(array.clone());
    	}
    }
    let mut r : Vec<RistrettoPoint> =  Vec::new();
    for j in 0..2 {
    	r.push(CompressedRistretto(p[j]).decompress().unwrap());
    }
    let z = Scalar::from_bytes_mod_order(p[2]);
    
    return ZeroKnowledgeProofOpen{ commitments: r, response: z };
}

// Write the proof of opening with LDP in a file:
fn writeproofopenldp(p: &ZeroKnowledgeProofOpenLDP) -> io::Result<()>{
    let mut proof: Vec<[u8; 32]> = Vec::new();
    let mut file = File::options().write(true).truncate(true).create(true).open("proofopeningldp.txt")?;
    
    match p {
    	ZeroKnowledgeProofOpenLDP{ commitments0, challenge0, response0, commitments1, challenge1, responses1 } => {
	    for j in 0..commitments0.len(){
    	    	proof.push(((commitments0[j]).compress()).to_bytes());
    	    }
    	    proof.push((challenge0).to_bytes());
    	    proof.push((response0).to_bytes());
    	    for j in 0..commitments1.len(){
    	    	proof.push(((commitments1[j]).compress()).to_bytes());
    	    }
    	    proof.push((challenge1).to_bytes());
    	    for j in 0..responses1.len(){
    	    	proof.push((responses1[j]).to_bytes());
    	    }
    	}
    }	    
    for k in 0..proof.len(){
        file.write_vectored(&[IoSlice::new(&proof[k])])?;
    }
    return Ok(())
} 

// Read the proof of opening located in a file.
fn exportproofopenldp() -> ZeroKnowledgeProofOpenLDP{
    let mut buffer = Vec::new();
    let file = File::open("proofopeningldp.txt"); 
    let _= file.expect("REASON").read_to_end(&mut buffer); 
    let mut p : Vec<[u8; 32]> = Vec::new();
    let mut array = [0u8; 32];
    for i in 0..buffer.len(){
    	array[i % 32] = buffer[i];
    	if i % 32 == 31 && i > 0{
    		p.push(array.clone());
    	}
    }
    
    let mut r0 : Vec<RistrettoPoint> =  Vec::new();
    let mut r1 : Vec<RistrettoPoint> =  Vec::new();
    let mut z1 : Vec<Scalar> =  Vec::new();
    for j in 0..3 {
    	r0.push(CompressedRistretto(p[j]).decompress().unwrap());
    }
    let c0 = Scalar::from_bytes_mod_order(p[3]);
    let z0 = Scalar::from_bytes_mod_order(p[4]);
    for j in 5..11 {
    	r1.push(CompressedRistretto(p[j]).decompress().unwrap());
    }
    let c1 = Scalar::from_bytes_mod_order(p[11]);
    for j in 12..14 {
    	z1.push(Scalar::from_bytes_mod_order(p[j]));
    }
    
    return ZeroKnowledgeProofOpenLDP{ commitments0: r0, challenge0: c0, response0: z0, commitments1: r1, challenge1: c1, responses1: z1 };
}

// Functions for measuring the elapsed time between each algorithm:
pub fn measure_time(iter: u32, l_1: usize, l_2: usize) {

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
   	let set = setup(&mut csrng, l_1, l_2); 
   	let duration_setup = start_setup.elapsed();
   	time_setup += duration_setup;
   	let _ = writesetup(&set);
        let newset = exportsetup();
        
        assert!(newset == set, "The setup in the file in not equal to the real setup");
    	let setdata = fs::metadata("setup.txt");
    	setsize += setdata.expect("REASON").len(); 	
   		
    	let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	let m = rand_bitstring(l_2);
    	
    	// Commit:
    	let start_commit = Instant::now();
    	let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	let duration_commit = start_commit.elapsed();
   	time_commit += duration_commit;
   	
    	let k = comm.0;
    	let c = comm.1;
    	let p_comm = comm.2;
    	
    	let _ = writecommit(&c);
        let newc = exportcommit(l_1, l_2);
        assert!(newc == c, "The commitment in the file in not equal to the real commitment");
    	let comdata = fs::metadata("commitment.txt");
    	comsize += comdata.expect("REASON").len();
    	
    	let _ = writeproofcommit(&p_comm, l_1, l_2);
        let new_pcomm = exportproofcommit(l_1, l_2);
        assert!(new_pcomm == p_comm, "The proof of commitment in the file in not equal to the real proof of commitment");
    	let pcomdata = fs::metadata("proofcommitment.txt");
    	pcomsize += pcomdata.expect("REASON").len();
    	
    	// Ver_Commit:
    	let start_ver_commit = Instant::now();
    	let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
    	let duration_ver_commit = start_ver_commit.elapsed();
    	time_ver_commit += duration_ver_commit;
    	
    	assert!(b_comm == true, "Ver_Commit != 1 \n");
    
    	// Open:
    	let start_open = Instant::now();
    	let opening = open(&mut csrng, set.clone(), k, c.clone());
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
	let hat_theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	
    	let start_openldp = Instant::now();
    	let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), hat_theta.clone());
    	let duration_openldp = start_openldp.elapsed();
    	time_openldp += duration_openldp;
    	
    	let hat_m = openingldp.0;
    	let vec_h = openingldp.1;
    	let vec_y_p = openingldp.2;
    	let p_openldp = openingldp.3;
    	
    	let _ = writeproofopenldp(&p_openldp);
        let new_popenldp = exportproofopenldp();
        assert!(new_popenldp == p_openldp, "The proof of opening with ldp in the file in not equal to the real proof of opening with ldp");
    	let popenldpdata = fs::metadata("proofopeningldp.txt");
    	popenldpsize += popenldpdata.expect("REASON").len();
    	
    	// Ver_Openldp:
    	let start_ver_openldp = Instant::now();
    	let b_openldp = ver_openldp(set.clone(), c.clone(), (&hat_m).to_vec(), (&vec_h).to_vec(), (&vec_y_p).to_vec(), p_openldp, hat_theta.clone());
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
    
    println!("Average running time over {:?} iterations with l1 = {:?} and l2 = {:?}:", iter, l_1, l_2);
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
