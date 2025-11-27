use std::collections::HashMap;

use anyhow::Result;

use crate::vm::Value;

pub type HeapPtr = u64;

#[derive(Clone, Debug)]
pub struct HeapObject {
    pub value: Value,
    pub owning_scope: usize,
    pub ref_count: usize,
}

#[derive(Debug)]
pub struct Heap {
    objects: HashMap<HeapPtr, HeapObject>,
    next_ptr: HeapPtr,
    scope_objects: HashMap<usize, Vec<HeapPtr>>,
    current_scope: usize,
    next_scope_id: usize,
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

impl Heap {
    pub fn new() -> Self {
        Self {
            objects: HashMap::new(),
            next_ptr: 0,
            scope_objects: HashMap::new(),
            current_scope: 0,
            next_scope_id: 1,
        }
    }

    pub fn enter_scope(&mut self) -> usize {
        let scope_id = self.next_scope_id;
        self.next_scope_id += 1;
        self.current_scope = scope_id;
        self.scope_objects.insert(scope_id, Vec::new());
        scope_id
    }

    pub fn exit_scope(&mut self, scope_id: usize) {
        if let Some(objects) = self.scope_objects.remove(&scope_id) {
            for ptr in objects {
                if let Some(obj) = self.objects.get(&ptr)
                    && obj.ref_count == 0
                {
                    self.objects.remove(&ptr);
                }
            }
        }

        if self.current_scope > 0 {
            self.current_scope -= 1;
        }
    }

    pub fn allocate(&mut self, value: Value) -> HeapPtr {
        let ptr = self.next_ptr;
        self.next_ptr += 1;

        let obj = HeapObject {
            value,
            owning_scope: self.current_scope,
            ref_count: 0,
        };

        self.objects.insert(ptr, obj);

        self.scope_objects
            .entry(self.current_scope)
            .or_default()
            .push(ptr);

        ptr
    }

    pub fn get(&self, ptr: HeapPtr) -> Option<&Value> {
        self.objects.get(&ptr).map(|obj| &obj.value)
    }

    pub fn get_mut(&mut self, ptr: HeapPtr) -> Option<&mut Value> {
        self.objects.get_mut(&ptr).map(|obj| &mut obj.value)
    }

    pub fn set(&mut self, ptr: HeapPtr, value: Value) -> Result<()> {
        if let Some(obj) = self.objects.get_mut(&ptr) {
            obj.value = value;
            Ok(())
        } else {
            Err(anyhow::anyhow!("Invalid heap pointer: {ptr}"))
        }
    }

    pub fn incr_ref(&mut self, ptr: HeapPtr) {
        if let Some(obj) = self.objects.get_mut(&ptr) {
            obj.ref_count += 1;
        }
    }

    pub fn decr_ref(&mut self, ptr: HeapPtr) {
        if let Some(obj) = self.objects.get_mut(&ptr)
            && obj.ref_count > 0
        {
            obj.ref_count -= 1;
        }
    }

    pub fn free(&mut self, ptr: HeapPtr) -> Result<()> {
        if self.objects.remove(&ptr).is_some() {
            Ok(())
        } else {
            Err(anyhow::anyhow!("Invalid heap pointer: {ptr}"))
        }
    }
}
