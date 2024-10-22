use cryptocommit::measure_time;

fn main() {
    println!("Execution in progress...");
    println!("(It can take a long time)");
    let iter = 1000;
    let l1 = 4;
    let l2 = 4;
    measure_time(iter, l1, l2);	
}
