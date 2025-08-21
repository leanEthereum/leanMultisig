use p3_field::Field;
use rayon::prelude::*;
use whir_p3::poly::dense::WhirDensePolynomial;

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

type CacheKey = (TypeId, usize);

static SELECTORS_CACHE: OnceLock<
    Mutex<HashMap<CacheKey, Arc<OnceLock<Arc<dyn Any + Send + Sync>>>>>,
> = OnceLock::new();

pub fn univariate_selectors<F: Field>(n: usize) -> Arc<Vec<WhirDensePolynomial<F>>> {
    let key = (TypeId::of::<F>(), n);
    let mut map = SELECTORS_CACHE
        .get_or_init(|| Mutex::new(HashMap::new()))
        .lock()
        .unwrap();
    let cell = map
        .entry(key)
        .or_insert_with(|| Arc::new(OnceLock::new()))
        .clone();
    cell.get_or_init(|| {
        let v: Vec<WhirDensePolynomial<F>> = (0..(1 << n))
            .into_par_iter()
            .map(|i| {
                let values = (0..(1 << n))
                    .map(|j| (F::from_u64(j as u64), if i == j { F::ONE } else { F::ZERO }))
                    .collect::<Vec<_>>();
                WhirDensePolynomial::lagrange_interpolation(&values).unwrap()
            })
            .collect();
        Arc::new(v) as Arc<dyn Any + Send + Sync>
    })
    .clone()
    .downcast::<Vec<WhirDensePolynomial<F>>>()
    .unwrap()
}
