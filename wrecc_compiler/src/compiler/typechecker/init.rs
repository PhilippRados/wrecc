//! Functionality used in typechecker to initialize an aggregate type

use crate::compiler::common::types::*;
use crate::compiler::typechecker::mir::expr::Expr;

/// Helper object to store elements when initializing aggregate objects like:
/// `int array[10] = {1,2,[6] = 8}`
/// and keeping track of nested initializations
#[derive(Clone)]
pub struct CurrentObjects(pub Vec<(i64, i64, QualType)>);
impl CurrentObjects {
    pub fn new(qtype: QualType) -> Self {
        CurrentObjects(vec![(0, 0, qtype)])
    }
    /// Updates current-objects when encountering designator
    pub fn update(&mut self, (i, union_index, new_type): (i64, i64, QualType)) {
        self.0.last_mut().unwrap().0 = i;
        self.0.last_mut().unwrap().1 = union_index;
        self.0.push((0, 0, new_type));
    }
    pub fn current(&self) -> &(i64, i64, QualType) {
        self.0.last().unwrap()
    }
    pub fn current_type(&mut self) -> &mut QualType {
        if let Some((.., type_decl)) = self.0.last_mut() {
            type_decl
        } else {
            unreachable!("always at least one current objects")
        }
    }
    /// Returns overall offset up until current-objects
    pub fn offset(&self) -> i64 {
        self.0
            .iter()
            .fold(0, |acc, (i, _, qtype)| acc + qtype.ty.offset(*i))
    }
    /// Checks how much of a sub-type is already initialized and what new current-objects should be
    pub fn update_current(&mut self) {
        let mut remove_idx = None;
        for (obj_index, (i, _, qtype)) in self.0.iter().enumerate().rev() {
            // if unknown array-size then object can never be full
            if let Type::Array(_, ArraySize::Unknown) = qtype.ty {
                break;
            }
            if obj_index != 0 && (i + 1 >= qtype.ty.len() as i64) {
                remove_idx = Some(obj_index);
            } else {
                break;
            }
        }
        // if new current objects also full then remove too
        if let Some(i) = remove_idx {
            self.0.truncate(i);
        }

        // increment the index of the current object
        self.0.last_mut().unwrap().0 += 1;
    }

    /// Removes all objects except base-type
    pub fn clear(&mut self) {
        self.0.truncate(1);
    }

    /// Checks if this union has already been initialized and if so returns its size
    pub fn find_same_union(&self, new_list: &Vec<(CurrentObjects, Expr, i64)>) -> Option<(i64, usize)> {
        for (objects, ..) in new_list {
            let mut offset = 0;
            for (other_obj, current_obj) in objects.0.iter().zip(&self.0) {
                match (other_obj, current_obj) {
                    (
                        (_, i1, qtype @ QualType { ty: Type::Union(_), .. }),
                        (_, i2, QualType { ty: Type::Union(_), .. }),
                    ) if i1 != i2 => {
                        // allowed call `size()` bc unions cannot contain unbounded array
                        return Some((offset, qtype.ty.size()));
                    }
                    ((i1, ..), (i2, ..)) if *i1 != *i2 => break,
                    ((i, _, qtype), ..) => offset += qtype.ty.offset(*i),
                }
            }
        }
        None
    }
}

impl QualType {
    /// Returns the type of the field at index
    pub fn at(&self, index: usize) -> Option<QualType> {
        match &self.ty {
            Type::Array(of, ArraySize::Known(size)) => {
                if index >= *size {
                    None
                } else {
                    Some(of.as_ref().clone())
                }
            }
            Type::Array(of, ArraySize::Unknown) => Some(of.as_ref().clone()),
            Type::Struct(s) => s.members().get(index).map(|(ty, _)| ty.clone()),
            Type::Union(s) => {
                if index > 0 {
                    None
                } else {
                    s.members().first().map(|(ty, _)| ty.clone())
                }
            }
            _ => Some(self.clone()),
        }
    }
}

impl Type {
    /// Returns the number of top level elements of type
    pub fn len(&self) -> usize {
        match self {
            Type::Array(_, ArraySize::Known(size)) => *size,
            Type::Array(_, ArraySize::Unknown) => {
                unreachable!("unknown array-size is caught in update-current")
            }
            Type::Struct(s) => s.members().len(),
            _ => 1,
        }
    }

    /// Calculates offset in typesize until given index
    pub fn offset(&self, index: i64) -> i64 {
        match self {
            Type::Struct(s) => s
                .members()
                .iter()
                .take(index as usize)
                .fold(0, |acc, (m_type, _)| acc + m_type.ty.size() as i64),
            Type::Array(of, _) => of.ty.size() as i64 * index,
            _ => 0,
        }
    }
}
