use cryptocommit::measure_time;

fn main() {
    println!("Execution in progress...");
    println!("(It can take a long time)");
    let iter = 10;
    let n1 = 16; 
    let n2 = 16;
    measure_time(iter, n1, n2);	
}
