//! SCRATCH (not committed): per-case allocation + latency probe for perf work.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use cobra_testkit::{parse_dataset, run_case};

static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
const NBUCKETS: usize = 28;
static HIST_CNT: [AtomicU64; NBUCKETS] = [const { AtomicU64::new(0) }; NBUCKETS];
static HIST_ON: AtomicU64 = AtomicU64::new(0);

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::Relaxed);
        let sz = l.size();
        BYTES.fetch_add(sz as u64, Ordering::Relaxed);
        if HIST_ON.load(Ordering::Relaxed) != 0 {
            let b = ((usize::BITS - (sz.max(1) - 1).leading_zeros()) as usize).min(NBUCKETS - 1);
            HIST_CNT[b].fetch_add(1, Ordering::Relaxed);
        }
        System.alloc(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l);
    }
}

#[global_allocator]
static A: Counting = Counting;

fn main() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

fn run() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: allocprobe <file> [reps]");
    let reps: u64 = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(50)
        .max(1); // guard against `reps = 0` → divide-by-zero below
    let body = std::fs::read_to_string(&path).unwrap();
    let cases = parse_dataset(&body);
    for (i, case) in cases.iter().enumerate() {
        let _ = run_case(case, 64);
        let a0 = ALLOCS.load(Ordering::Relaxed);
        let b0 = BYTES.load(Ordering::Relaxed);
        let t = Instant::now();
        for _ in 0..reps {
            let _ = run_case(case, 64);
        }
        let dt = t.elapsed().as_secs_f64() / reps as f64;
        let a = (ALLOCS.load(Ordering::Relaxed) - a0) / reps;
        let b = (BYTES.load(Ordering::Relaxed) - b0) / reps;
        println!(
            "case{} line{}: {:.2}ms  allocs={}  churn={:.1}MB",
            i + 1,
            case.line_number,
            dt * 1e3,
            a,
            b as f64 / 1e6,
        );
    }
    if let Some(case) = cases.first() {
        for b in &HIST_CNT {
            b.store(0, Ordering::Relaxed);
        }
        HIST_ON.store(1, Ordering::Relaxed);
        let _ = run_case(case, 64);
        HIST_ON.store(0, Ordering::Relaxed);
        println!("--- case1 size histogram (count by 2^k bucket) ---");
        for (i, c) in HIST_CNT.iter().enumerate() {
            let cnt = c.load(Ordering::Relaxed);
            if cnt != 0 {
                println!("  <={:>7}: {}", 1usize << i, cnt);
            }
        }
    }
}
