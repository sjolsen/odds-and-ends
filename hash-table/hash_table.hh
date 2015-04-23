#ifndef HASH_TABLE_HH
#define HASH_TABLE_HH

#include "unordered_bucket.hh"
#include <functional>
#include <vector>
#include <ratio>
#include <cassert>
#include <limits>

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

	hash_table (size_type log2_buckets)
	// Checked precondition: 2 ^ log2_buckets is representable in size_type
	{
		assert (log2_buckets < std::numeric_limits <size_type>::digits);
		_storage.resize (size_type {1} << log2_buckets);
	}

	size_type _buckets () const
	{
		return _storage.size ();
	}

	bucket_type& _map_to_bucket (const key_type& key)
	{
		return _storage [_hash (key) % _buckets ()];
	}

public:
	hash_table ()
		: hash_table (4)
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
		return where.bucket->insert (where.index, std::move (key), std::move (value));
	}

	value_type& access (index_type where)
	// Precondition: where.index is a valid argument to where.bucket.access
	{
		return where.bucket->access (where.index);
	}
};

#endif
