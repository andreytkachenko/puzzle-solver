use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Default")]
    Default,
}

impl From<()> for Error {
    fn from(_: ()) -> Self {
        Self::Default
    }
}
