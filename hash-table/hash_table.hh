#ifndef HASH_TABLE_HH
#define HASH_TABLE_HH

#include "unordered_bucket.hh"
#include <functional>
#include <vector>
#include <ratio>

template <typename Key,
          typename Value,
          typename Hash = std::hash <Key>,
          typename Bucket = unordered_bucket <Key, Value>,
          typename Load_limit = std::ratio <4, 5> >
class hash_table
{
public:
	using key_type      = Key;
	using value_type    = Value;
	using hash_type     = Hash;
	using bucket_type   = Bucket;
	using storage_type  = std::vector <bucket_type>;
	using size_type     = typename storage_type::size_type;

	struct index_type
	{
	private:
		friend hash_table;
		using subindex_type = typename bucket_type::index_type;

		bucket_type* bucket;
		subindex_type index;

		index_type (bucket_type& bucket, subindex_type index)
			: bucket (&bucket),
			  index (index)
		{
		}
	};

	struct search_result
	{
		bool found;
		index_type where;
	};

private:
	storage_type _storage;
	size_type _elements;
	hash_type _hash;

	hash_table (size_type buckets)
	// Checked precondition: buckets is a power of 2
		: _storage (buckets),
		  _elements (0),
		  _hash {}
	{
	}

	size_type _buckets () const
	{
		return _storage.size ();
	}

	bool _load_limit_exceeded () const
	{
		auto load_factor = static_cast <double> (_elements) / _buckets ();
		auto load_limit  = static_cast <double> (Load_limit::num) / Load_limit::den;
		return load_factor > load_limit;
	}

	bucket_type& _map_to_bucket (const key_type& key)
	{
		return _storage [_hash (key) % _buckets ()];
	}

	value_type* _rehash (size_type buckets, value_type* addr)
	// Precondition: buckets is a valid constructor argument
	// Precondition: buckets > _buckets ()
	// Precondition: addr points to a value in the table
	// Postcondition: returns the new location of *addr
	{
		hash_table new_table (buckets);
		value_type* new_addr = nullptr;
		for_each ([&new_table, &new_addr, addr] (const key_type& key, value_type& value) {
			bool is_addr = &value == addr;
			auto result = new_table.search (key);
			auto& ref = new_table.insert (result.where, key, std::move (value));
			if (is_addr)
				new_addr = &ref;
		});
		*this = std::move (new_table);
		return new_addr;
	}

public:
	hash_table ()
		: hash_table (16)
	{
	}

	hash_table (hash_table&&) = default;
	hash_table (const hash_table&) = default;
	hash_table& operator = (hash_table&&) = default;
	hash_table& operator = (const hash_table&) = default;

	search_result search (const key_type& key)
	{
		auto& bucket = _map_to_bucket (key);
		auto result = bucket.search (key);
		auto found = result.found;
		auto where = index_type {bucket, result.where};
		return {found, where};
	}

	value_type& insert (index_type where, key_type key, value_type value)
	// Precondition: search (key) = {false, where}
	{
		auto* result = &where.bucket->insert (where.index, std::move (key), std::move (value));
		++_elements;
		if (_load_limit_exceeded ())
			result = _rehash (2 * _buckets (), result);
		return *result;
	}

	value_type& access (index_type where)
	// Precondition: where.index is a valid argument to where.bucket.access
	{
		return where.bucket->access (where.index);
	}

	template <typename Pair_func>
	void for_each (Pair_func f)
	{
		for (auto& bucket : _storage)
			bucket.for_each (f);
	}

	template <typename Pair_func>
	void for_each (Pair_func f) const
	{
		for (auto& bucket : _storage)
			bucket.for_each (f);
	}
};

#endif
