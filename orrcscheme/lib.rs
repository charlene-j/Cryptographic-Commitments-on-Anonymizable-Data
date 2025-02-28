mod commitscheme;
pub use crate::commitscheme::*;

#[cfg(test)]
mod tests{

    use rand_core::OsRng;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    use super::commitscheme::{ rand_bitstring, setup, commit, ver_commit, open, ver_open, openldp, ver_openldp, gen, sign, ver };

    // Test the algorithm Setup, Commit, Ver_Commit, Open, Ver_Open, Openldp, Ver_Openldp:
	
    #[test]    
    fn test1() { // hat_theta = theta.
        let mut csrng = OsRng; 
    
        let l_1 = 8;
        let l_2 = 8;
    
        // Setup:
        let set = setup(&mut csrng, l_1, l_2); 
    
        let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
        print!("theta: {:?}", theta);
        let m = rand_bitstring(l_2);
        print!("m: {:?}\n", m);
    
        // Commit:
        let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	
        let k = comm.0;
        let c = comm.1;
        let p_comm = comm.2;
        let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
        assert!(b_comm == true, "Ver_Commit != 1 \n");
    
        // Open:
        let opening = open(&mut csrng, set.clone(), k, c.clone());
        let m_open = opening.0;
        let p_open = opening.1;
        let b_open = ver_open(set.clone(), c.clone(), m.clone(), p_open);
        assert!(m == m_open, "The opened message is not equal to the original message \n");
        assert!(b_open == true, "Ver_Open != 1 \n");
    
        // Openldp with hat_theta = theta:
        let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), theta.clone());
        let hat_m = openingldp.0;
        println!("hat_m: {:?}\n", hat_m);
        let vec_h = openingldp.1;
        let vec_y_p = openingldp.2;
        assert!(m == hat_m,"The opened message with ldp is not equal to the original message \n");
        let p_openldp = openingldp.3;
        let b_openldp = ver_openldp(set.clone(), c.clone(), (&hat_m).to_vec(), (&vec_h).to_vec(), (&vec_y_p).to_vec(), p_openldp, theta.clone());
        assert!(b_openldp == true, "Ver_Openldp != 1 \n"); 	
    }
    
    #[test]
    fn test2() { // hat_theta = (hat_s, hat_t) and theta = (s,t) and hat_s = s.
    
    	let mut csrng = OsRng; 
    
    	let l_1 = 20;
    	let l_2 = 20;
    
    	// Setup:
    	let set = setup(&mut csrng, l_1, l_2); 
    
    	let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	println!("theta: {:?}", theta);
    	let m = rand_bitstring(l_2);
    	println!("m: {:?}\n", m);
    
    	// Commit:
    	let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	let k = comm.0;
    	let c = comm.1;
    	let p_comm = comm.2;
    	let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
    	assert!(b_comm == true, "Ver_Commit != 1 \n");
    
    	// Open:
    	let opening = open(&mut csrng, set.clone(), k, c.clone());
    	let m_open = opening.0;
    	let p_open = opening.1;
    	let b_open = ver_open(set.clone(), c.clone(), m.clone(), p_open);
    	assert!(m == m_open, "The opened message is not equal to the original message \n");
    	assert!(b_open == true, "Ver_Open != 1 \n");
    
	// Openldp with hat_theta = theta:
	let hat_theta = vec![(&theta[0]).to_vec(), rand_bitstring(l_2)];
    	let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), (&hat_theta).to_vec());
    	let hat_m = openingldp.0;
    	println!("hat_m: {:?}\n", hat_m);
    	let vec_h = openingldp.1;
    	let vec_y_p = openingldp.2;
    	assert!(m == hat_m,"The opened message with ldp is not equal to the original message \n");
    	let p_openldp = openingldp.3;
    	let b_openldp = ver_openldp(set.clone(), c.clone(), (&hat_m).to_vec(), (&vec_h).to_vec(), (&vec_y_p).to_vec(), p_openldp, (&hat_theta).to_vec());
    	assert!(b_openldp == true, "Ver_Openldp != 1 \n");	
    }
    
    #[test]
    fn test3() { // with hat_theta = (hat_s, hat_t) and theta = (s,t) and m = t ^ hat_t.
    
    	let mut csrng = OsRng; 
    
    	let l_1 = 7;
    	let l_2 = 7;
    
    	// Setup:
    	let set = setup(&mut csrng, l_1, l_2); 
    
    	let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	println!("theta: {:?}", theta);
    	let m = rand_bitstring(l_2);
    	println!("m: {:?}\n", m);
    
    	// Commit:
    	let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	let k = comm.0;
    	let c = comm.1;
    	let p_comm = comm.2;
    	let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
    	assert!(b_comm == true, "Ver_Commit != 1 \n");
    
    	// Open:
    	let opening = open(&mut csrng, set.clone(), k, c.clone());
    	let m_open = opening.0;
    	let p_open = opening.1;
    	let b_open = ver_open(set.clone(), c.clone(), m.clone(), p_open);
    	assert!(m == m_open, "The opened message is not equal to the original message \n");
    	assert!(b_open == true, "Ver_Open != 1 \n");
    
	// Openldp with hat_theta = theta:
	let mut hat_t: Vec<usize> = Vec::new();
	for i in 0..l_2 {
	    hat_t.push(m[i] ^ theta[0][i]);
	}
	let hat_theta = vec![(&theta[0]).to_vec(), hat_t];
    	let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), (&hat_theta).to_vec());
    	let hat_m = openingldp.0;
    	println!("hat_m: {:?}\n", hat_m);
    	let vec_h = openingldp.1;
    	let vec_y_p = openingldp.2;
    	assert!(m == hat_m,"The opened message with ldp is not equal to the original message \n");
    	let p_openldp = openingldp.3;
    	let b_openldp = ver_openldp(set.clone(), c.clone(), (&hat_m).to_vec(), (&vec_h).to_vec(), (&vec_y_p).to_vec(), p_openldp, (&hat_theta).to_vec());
    	assert!(b_openldp == true, "Ver_Openldp != 1 \n");	
    }
    
    #[test]
    fn test4(){ // hat_theta != theta.
    	let mut csrng = OsRng; 
    
    	let l_1 = 7;
    	let l_2 = 7;
    
    	// Setup:
    	let set = setup(&mut csrng, l_1, l_2); 
    
    	let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	println!("theta: {:?}", theta);
    	let m = rand_bitstring(l_2);
    	println!("m: {:?}\n", m);
    
    	// Commit:
    	let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	let k = comm.0;
    	let c = comm.1;
    	let p_comm = comm.2;
    	let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
    	assert!(b_comm == true, "Ver_Commit != 1 \n");
    
    	// Open:
    	let opening = open(&mut csrng, set.clone(), k, c.clone());
    	let m_open = opening.0;
    	let p_open = opening.1;
    	let b_open = ver_open(set.clone(), c.clone(), m.clone(), p_open);
    	assert!(m == m_open, "The opened message is not equal to the original message \n");
    	assert!(b_open == true, "Ver_Open != 1 \n");
    
	// Openldp with hat_theta != theta:
	let mut hat_theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
	while &hat_theta[0] == &theta[0] || &hat_theta[1] == &theta[1] {
	    hat_theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
	}
    	println!("hat_theta: {:?}", hat_theta);
    	let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), hat_theta.clone());
    	let hat_m = openingldp.0;
    	println!("hat_m: {:?}\n", hat_m);
    	for i in 0..hat_m.len(){
    	    assert!(hat_m[i] == &hat_theta[1][i] ^ &theta[1][i], "hat_m != t xor hat_t{}",i);
    	}
    	let vec_h = openingldp.1;
    	let vec_y_p = openingldp.2;
    	let p_openldp = openingldp.3;
    	let b_openldp = ver_openldp(set.clone(), c.clone(), (&hat_m).to_vec(), (&vec_h).to_vec(), (&vec_y_p).to_vec(), p_openldp, hat_theta.clone());
    	assert!(b_openldp == true, "Ver_Openldp != 1 \n");   	
    }
       
    #[test]
    fn test5() { // hat_theta != theta and len(s) != len(t).
    	let mut csrng = OsRng; 
    
    	let l_1 = 3;
    	let l_2 = 7;
    
    	// Setup:
    	let set = setup(&mut csrng, l_1, l_2); 
    
    	let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	println!("theta: {:?}", theta);
    	let m = rand_bitstring(l_2);
    	println!("m: {:?}\n", m);
    
    	// Commit:
    	let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	let k = comm.0;
    	let c = comm.1;
    	let p_comm = comm.2;
    	let b_comm = ver_commit(set.clone(), c.clone(), p_comm);
    	assert!(b_comm == true, "Ver_Commit != 1 \n");
    
    	// Open:
    	let opening = open(&mut csrng, set.clone(), k, c.clone());
    	let m_open = opening.0;
    	let p_open = opening.1;
    	let b_open = ver_open(set.clone(), c.clone(), m.clone(), p_open);
    	assert!(m == m_open, "The opened message is not equal to the original message \n");
    	assert!(b_open == true, "Ver_Open != 1 \n");
    
	// Openldp with hat_theta != theta:
	let mut hat_theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
	while hat_theta == theta {
	    hat_theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
	}
    	println!("theta: {:?}", hat_theta);
    	let openingldp = openldp(&mut csrng, set.clone(), k, c.clone(), hat_theta.clone());
    	let hat_m = openingldp.0;
    	println!("hat_m: {:?}\n", hat_m);
    	let vec_h = openingldp.1;
    	let vec_y_p = openingldp.2;
    	let p_openldp = openingldp.3;
    	let b_openldp = ver_openldp(set.clone(), c.clone(), (&hat_m).to_vec(), (&vec_h).to_vec(), (&vec_y_p).to_vec(), p_openldp, hat_theta.clone());
    	assert!(b_openldp == true, "Ver_Openldp != 1 \n");   	
    }

    // Test the algorithm Sign and Verify:
           
    #[test]
    fn test_signature() {
    
    	let mut csrng = OsRng; 
    
    	let l_1 = 7;
    	let l_2 = 7;
    
    	// Setup:
    	let set = setup(&mut csrng, l_1, l_2); 
    
    	let theta = vec![rand_bitstring(l_1), rand_bitstring(l_2)];
    	println!("theta: {:?}", theta);
    	let m = rand_bitstring(l_2);
    	println!("m: {:?}\n", m);
    
    	// Commit:
    	let comm = commit(&mut csrng, set.clone(), (&m).to_vec(), theta.clone());
    	let c = comm.1;
    	
    	// Generate public and secret keys:
	let (secret_key, public_key) = gen(& mut csrng, RISTRETTO_BASEPOINT_POINT);
		
	// Generate a signature:	    	
	let sig = sign(&mut csrng, c.clone(), RISTRETTO_BASEPOINT_POINT, public_key, secret_key);

	// Verify the Signature:   	    	
	let verify = ver(c.clone(), RISTRETTO_BASEPOINT_POINT, public_key, sig);
			
	assert!(verify == true, "Ver != 1 \n"); 
    } 
} 
