// Copyright 1996  Michael E. Stillman

// This should probably be done by:
// (a) making a type GBRing, that FreeModule, and res_poly
//     both can inherit from: but this is a bit of a kludge...
// (b) making a vector type with a next and coeff field, that
//     is then inherited by vecterm, resterm.
// Redefine:
// GBRing
//    routines that should be implemented in this class:
//    add_to, compare, get_ring, remove
// gbvector *
//    fields of this structure type should include:
//    next, coeff

// GEOHEAP_SIZE: defined in style.hpp
// heap_size: defined in object.cpp

class gbvectorHeap
{
  GBRing *F;		// Our elements will be vectors in here
  const Ring *K;		// The coefficient ring
  gbvector * heap[GEOHEAP_SIZE];
  int top_of_heap;
  int mLead;			// set after a call to get_lead_term.
				// set negative after each call to add, 
				// or remove_lead_term
public:
  gbvectorHeap(GBRing *F);
  ~gbvectorHeap();

  void add(gbvector * p);
  const gbvector * get_lead_term(); // Returns NULL if none.
  gbvector * remove_lead_term();	// Returns NULL if none.

  GBRing *get_target() const { return F; }
  gbvector * value();		// Returns the linearized value, and resets the gbvectorHeap.

  gbvector * debug_list(int i) { return heap[i]; } // DO NOT USE, except for debugging purposes!
  gbvector * current_value() const; // Adds up all the elements and returns this value
				 // Mainly used for debugging.
};

inline gbvectorHeap::gbvectorHeap(GBRing *FF)
: F(FF),
  K(FF->get_ring()->getCoefficientRing()),
  top_of_heap(-1),
  mLead(-1)
{
  // set K
  int i;
  for (i=0; i<GEOHEAP_SIZE; i++)
    heap[i] = NULL;
}

inline gbvectorHeap::~gbvectorHeap()
{
  // The user of this class must insure that all 'vecterm's
  // have been removed first.  Thus, we don't need to
  // do anything here.
}

inline void gbvectorHeap::add(gbvector * p)
{
  mLead = -1;
  int len = F->n_terms(p);
  int i= 0;
  while (len >= heap_size[i]) i++;
  F->add_to(heap[i], p);
  len = F->n_terms(heap[i]);
  p = NULL;
  while (len >= heap_size[i])
    {
      i++;
      F->add_to(heap[i], heap[i-1]);
      len = F->n_terms(heap[i]);
      heap[i-1] = NULL;
    }
  if (i > top_of_heap)
    top_of_heap = i;
}

inline const gbvector * gbvectorHeap::get_lead_term()
{
  int lead_so_far = -1;
  for (int i=0; i <= top_of_heap; i++)
    {
      if (heap[i] == NULL) continue;
      if (lead_so_far < 0) 
	{
	  lead_so_far = i;
	  continue;
	}
      int cmp = F->compare(heap[lead_so_far], heap[i]);
      if (cmp == GT) continue;
      if (cmp == LT)
	{
	  lead_so_far = i;
	  continue;
	}
      // At this point we have equality
      K->add_to(heap[lead_so_far]->coeff, heap[i]->coeff);
      gbvector * tmp = heap[i];
      heap[i] = tmp->next;
      tmp->next = NULL;
      F->remove(tmp);

      if (K->is_zero(heap[lead_so_far]->coeff))
	{
	  // Remove, and start over
	  tmp = heap[lead_so_far];
	  heap[lead_so_far] = tmp->next;
	  tmp->next = NULL;
	  F->remove(tmp);
	  lead_so_far = -1;
	  i = -1;
	}
    }
  mLead = lead_so_far;
  if (lead_so_far < 0) return NULL;
  gbvector * result = heap[lead_so_far];
  return result;
}
inline gbvector * gbvectorHeap::remove_lead_term()
{
  if (mLead < 0) get_lead_term();
  if (mLead < 0) return NULL;
  gbvector * result = heap[mLead];
  heap[mLead] = result->next;
  result->next = NULL;
  mLead = -1;
  return result;
}

inline gbvector * gbvectorHeap::value()
{
  gbvector * result = NULL;
  for (int i=0; i<=top_of_heap; i++)
    {
      if (heap[i] == NULL) continue;
      F->add_to(result, heap[i]);
      heap[i] = NULL;
    }
  top_of_heap = -1;
  return result;
}
inline gbvector * gbvectorHeap::current_value() const
{
  gbvector * result = NULL;
  for (int i=0; i<=top_of_heap; i++)
    {
      if (heap[i] == NULL) continue;
      gbvector * tmp = F->copy(heap[i]);
      F->add_to(result, tmp);
    }
  return result;
}

// Local Variables:
// compile-command: "make -C $M2BUILDDIR/Macaulay2/e "
// End:
