//! Debug Message Registry
//!
//! This module provides a thread-safe global registry for debug messages used during
//! WebAssembly code generation and execution. Debug messages are registered during
//! compilation and can be recalled later by their numeric ID.
//!
//! # Architecture
//!
//! The module uses a `LazyLock<Mutex<Vec<String>>>` to provide:
//! - Thread-safe access to the message store
//! - Lazy initialization on first use
//! - Persistent storage across the compilation lifetime
//!
//! # Usage
//!
//! ```ignore
//! use crate::debug_msg;
//!
//! // Register a debug message and get its ID
//! let id = debug_msg::register("Variable 'x' not found".to_string());
//!
//! // Later, recall the message by ID
//! debug_msg::recall(id, |msg| println!("Debug: {}", msg));
//! ```

#![allow(clippy::expect_used)]

use std::ops::Deref;
use std::sync::{LazyLock, Mutex};

/// Global thread-safe storage for debug messages.
static DEBUG_MSGS: LazyLock<Mutex<Vec<String>>> = LazyLock::new(Mutex::default);

/// Error message displayed when the mutex lock fails.
static LOCK_ERR: &str = "could not lock debug message mutex";

/// Error message displayed when a message ID is not found.
static MSG_ERR: &str = "could not find debug message";

/// Registers a debug message and returns its unique identifier.
///
/// Messages are stored in a global thread-safe vector. The returned ID
/// can be used later with [`recall`] to retrieve the message.
///
/// # Arguments
///
/// * `s` - The debug message string to register
///
/// # Returns
///
/// Returns the unique integer ID for the registered message.
///
/// # Panics
///
/// Panics if the mutex lock is poisoned.
pub(crate) fn register(s: String) -> i32 {
    let mut msgs = DEBUG_MSGS.lock().expect(LOCK_ERR);
    let id = msgs.len();
    msgs.push(s);
    id as i32
}

/// Recalls a previously registered debug message by its ID.
///
/// The message is passed to the provided closure for processing.
/// If the ID is invalid, a default error message is passed instead.
///
/// # Arguments
///
/// * `id` - The message ID returned by [`register`]
/// * `f` - A closure that receives the message string
///
/// # Panics
///
/// Panics if the mutex lock is poisoned.
pub(crate) fn recall<F: Fn(&str)>(id: i32, f: F) {
    f(DEBUG_MSGS
        .lock()
        .expect(LOCK_ERR)
        .get(id as usize)
        .map(Deref::deref)
        .unwrap_or(MSG_ERR))
}
