#[macro_export]
/// Macro to bench a function if feature "bench-internal" is enabled
/// This macro takes two types of inputs - those passed as references ($ref_var)
/// and those passed by value ($own_var). The input $batch_size determines the
/// size of the input, and it will tell criterion whether it can keep several
/// copies of the input in parallel runs.
macro_rules! bench_and_run {
    ($group:expr ;
    $( ref $ref_var:ident),* ;
     ;
    $name: literal ;
    $call:expr
    ) => {{
        #[cfg(feature = "bench-internal")]
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
        #[cfg(feature = "bench-internal")]
        {
            $group.bench_function($name, |b| {
                b.iter_batched(
                    || ($( $ref_var.clone(), )* $($own_var.clone(), )*),
                    |clones| {
                        let ($(mut $ref_var, )*$($own_var,)*) = clones;
                        let _ = $call($(&mut $ref_var, )* $( $own_var, )* );
                    },
                    criterion::BatchSize::LargeInput,
                )
            });
        }

        $call( $( $ref_var, )* $( $own_var, )* )
    }};
}
