error_chain! {
    types {
        Error, ErrorKind, ChainErr, Result;
    }

    links { }

    foreign_links {
        ::std::io::Error, IoError,
        "I/O error";
    }

    errors { }
}
