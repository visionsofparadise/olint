//! A counting global allocator: it forwards to the system allocator and tracks live and peak requested bytes with
//! atomics.
//!
//! The counts are requested layout sizes, not the system allocator's rounded block sizes, so they depend only on the
//! program's allocation sequence. `snapshot-member` runs one member per process, so the peak is that member's peak.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, Ordering};

pub struct Counting;

static LIVE: AtomicU64 = AtomicU64::new(0);
static PEAK: AtomicU64 = AtomicU64::new(0);

fn grow(bytes: u64) {
    let live = LIVE.fetch_add(bytes, Ordering::Relaxed) + bytes;

    PEAK.fetch_max(live, Ordering::Relaxed);
}

fn shrink(bytes: u64) {
    LIVE.fetch_sub(bytes, Ordering::Relaxed);
}

// SAFETY: every method forwards to `System` with the caller's layout and only adjusts counters beside it.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller upholds `GlobalAlloc::alloc`'s contract, which `System` shares.
        let pointer = unsafe { System.alloc(layout) };

        if !pointer.is_null() {
            grow(layout.size() as u64);
        }

        pointer
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as for `alloc`.
        let pointer = unsafe { System.alloc_zeroed(layout) };

        if !pointer.is_null() {
            grow(layout.size() as u64);
        }

        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        // SAFETY: `pointer` came from this allocator, hence from `System`, with `layout`.
        unsafe { System.dealloc(pointer, layout) };

        shrink(layout.size() as u64);
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: `pointer` came from `System` with `layout`, and the caller upholds `realloc`'s contract.
        let moved = unsafe { System.realloc(pointer, layout, new_size) };

        if !moved.is_null() {
            let old = layout.size() as u64;
            let new = new_size as u64;

            match new >= old {
                true => grow(new - old),
                false => shrink(old - new),
            }
        }

        moved
    }
}

/// Bytes currently allocated.
pub fn live() -> u64 {
    LIVE.load(Ordering::Relaxed)
}

/// The most bytes live at once since the process started or the last `reset_peak`.
pub fn peak() -> u64 {
    PEAK.load(Ordering::Relaxed)
}

/// Restarts peak tracking from the bytes live now.
pub fn reset_peak() {
    PEAK.store(live(), Ordering::Relaxed);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peak_covers_a_released_allocation() {
        reset_peak();

        let before = peak();
        let block = vec![0u8; 1 << 20];

        assert!(peak() >= before + (1 << 20));
        drop(block);
        assert!(peak() >= before + (1 << 20));
    }
}
