use p3_field::PrimeCharacteristicRing;

use crate::constant::F;

/// # Pad to Power of Two
///
/// A utility function that pads a slice of field elements with zeros to the next
/// power-of-two length.
///
/// ## Arguments
/// * `data`: A slice of field elements.
///
/// ## Returns
/// A new `Vec<F>` containing the original data, padded with zeros.
pub(crate) fn pad_to_power_of_two(data: &[F]) -> Vec<F> {
    // Calculate the next power-of-two length.
    let next_power_of_two = data.len().next_power_of_two();
    // Create a new vector from the input slice.
    let mut padded = data.to_vec();
    // Resize the vector to the target length, filling with zeros.
    padded.resize(next_power_of_two, F::ZERO);
    // Return the padded vector.
    padded
}
