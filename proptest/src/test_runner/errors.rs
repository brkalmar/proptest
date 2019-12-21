//-
// Copyright 2017, 2018 The proptest developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use crate::std_facade::fmt;

#[cfg(feature = "std")]
use std::string::ToString;

use crate::test_runner::Reason;

/// Errors which can be returned from test cases to indicate non-successful
/// completion.
///
/// Note that in spite of the name, `TestCaseError` is currently *not* an
/// instance of `Error`, since otherwise `impl<E : Error> From<E>` could not be
/// provided.
///
/// Any `Error` can be converted to a `TestCaseError`, which places
/// `Error::display()` into the `Fail` case.
#[derive(Debug, Clone)]
pub enum TestCaseError {
    /// The input was not valid for the test case. This does not count as a
    /// test failure (nor a success); rather, it simply signals to generate
    /// a new input and try again.
    Reject(Reason),
    /// The code under test failed the test.
    Fail(Reason),
}

impl TestCaseError {
    /// Rejects the generated test input as invalid for this test case. This
    /// does not count as a test failure (nor a success); rather, it simply
    /// signals to generate a new input and try again.
    ///
    /// The string gives the location and context of the rejection, and
    /// should be suitable for formatting like `Foo did X at {whence}`.
    pub fn reject(reason: impl Into<Reason>) -> Self {
        TestCaseError::Reject(reason.into())
    }

    /// The code under test failed the test.
    ///
    /// The string should indicate the location of the failure, but may
    /// generally be any string.
    pub fn fail(reason: impl Into<Reason>) -> Self {
        TestCaseError::Fail(reason.into())
    }
}

impl fmt::Display for TestCaseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TestCaseError::Reject(ref whence) => {
                write!(f, "Input rejected at {}", whence)
            }
            TestCaseError::Fail(ref why) => write!(f, "Case failed: {}", why),
        }
    }
}

#[cfg(feature = "std")]
impl<E: ::std::error::Error> From<E> for TestCaseError {
    fn from(cause: E) -> Self {
        TestCaseError::fail(cause.to_string())
    }
}

/// Convenience for the type returned by test cases.
pub type TestCaseResult = Result<(), TestCaseError>;

/// Implemented by types which can be converted to [`TestCaseResult`].
///
/// [`TestCaseResult`]: type.TestCaseResult.html
pub trait Testable {
    /// Convert to [`TestCaseResult`].
    ///
    /// [`TestCaseResult`]: type.TestCaseResult.html
    fn result(self) -> TestCaseResult;
}

impl Testable for () {
    fn result(self) -> TestCaseResult {
        Ok(())
    }
}

impl Testable for bool {
    fn result(self) -> TestCaseResult {
        if self {
            Ok(())
        } else {
            Err(TestCaseError::fail("returned false"))
        }
    }
}

impl<T, E> Testable for Result<T, E>
where
    T: Testable,
    E: Into<TestCaseError>,
{
    fn result(self) -> TestCaseResult {
        match self {
            Ok(t) => t.result(),
            Err(e) => Err(e.into()),
        }
    }
}

/// A failure state from running test cases for a single test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TestError<T> {
    /// The test was aborted for the given reason, for example, due to too many
    /// inputs having been rejected.
    Abort(Reason),
    /// A failing test case was found. The string indicates where and/or why
    /// the test failed. The `T` is the minimal input found to reproduce the
    /// failure.
    Fail(Reason, T),
}

impl<T: fmt::Debug> fmt::Display for TestError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TestError::Abort(ref why) => write!(f, "Test aborted: {}", why),
            TestError::Fail(ref why, ref what) => write!(
                f,
                "Test failed: {}; minimal failing input: {:?}",
                why, what
            ),
        }
    }
}

#[cfg(feature = "std")]
impl<T: fmt::Debug> ::std::error::Error for TestError<T> {
    fn description(&self) -> &str {
        match *self {
            TestError::Abort(..) => "Abort",
            TestError::Fail(..) => "Fail",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_case_result_testable() {
        is_testable::<TestCaseResult>();
    }

    #[test]
    fn result_with_test_case_error_testable() {
        is_testable::<Result<bool, TestCaseError>>();
        is_testable::<Result<TestCaseResult, TestCaseError>>();
    }

    #[cfg(feature = "std")]
    #[test]
    fn result_with_std_error_testable() {
        is_testable::<Result<bool, ::std::io::Error>>();
        is_testable::<Result<(), ::std::num::TryFromIntError>>();
    }

    fn is_testable<T: Testable>() {}
}
