use std::env::args;

fn main() {
    // Get args and return wc
    let args: Vec<String> = args().collect();
    if args.len() < 2 {
        println!("Usage: wc <string>");
        return;
    }
    // Implement wc
    let wc = args[1].split_whitespace().count();
    // let lc = args[1].lines().count();
    // let cc = args[1].chars().count();
    // println!("{lc} {wc} {cc}");
    println!("{}", wc);
}
