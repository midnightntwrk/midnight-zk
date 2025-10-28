#[macro_export]
/// Macro to bench a function if feature "bench-internal" is enabled
/// This macro takes two types of inputs - those passed as references ($ref_var)
/// and those passed by value ($own_var).
///
/// The macro uses `BatchSize::SmallInput` or `BatchSize::LargeInput` depending
/// on whether there are inputs passed by by value or not (inputs owned by the
/// inner functions are usually large polynomials). The only input that is
/// passed by reference is the transcript, as it is always used as a mutable
/// reference. We clone both the owned inputs as the transcript outside of the
/// scope that is being benchmarked.
macro_rules! bench_and_run {
    ($group:expr ;
    $( ref $ref_var:ident),* ;
     ;
    $name: literal ;
    $call:expr
    ) => {{
        #[cfg(all(test, feature = "bench-internal"))]
        {
            $group.bench_function($name, |b| {
                b.iter_batched(
                    || ($( $ref_var.clone(), )*),
                    |clones| {
                        let ($(mut $ref_var, )*) = clones;
                        let _ = $call($(&mut $ref_var, )* );
                    },
                    criterion::BatchSize::SmallInput,
                )
            });
        }

        $call( $( $ref_var, )* )
    }};

    ($group:expr ;
    $( ref $ref_var:ident),* ;
    $( own $own_var:ident),* ;
    $name: literal ;
    $call:expr
    ) => {{
        #[cfg(all(test, feature = "bench-internal"))]
        {
            $group.bench_function($name, |b| {
                b.iter_batched(
                    || ($( $ref_var.clone(), )* $($own_var.clone(), )*),
                    |clones| {
                        let ($(mut $ref_var, )*$($own_var,)*) = clones;
                        let _ = $call($(&mut $ref_var, )* $( $own_var, )* );
                    },
                    criterion::BatchSize::PerIteration,
                )
            });
        }

        $call( $( $ref_var, )* $( $own_var, )* )
    }};
}
