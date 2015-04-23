#ifndef ORDERED_BUCKET_HH
#define ORDERED_BUCKET_HH

#include "common.hh"
#include "binary-search.hh"
#include <vector>

template <typename Key, typename Value>
class ordered_bucket
{
public:
	using key_type     = Key;
	using value_type   = Value;
	using pair_type    = kv <key_type, value_type>;
	using storage_type = std::vector <pair_type>;

	struct index_type
	{
	private:
		friend ordered_bucket;
		using iterator = typename storage_type::iterator;

		iterator iter;

		index_type (iterator iter)
			: iter (iter)
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

public:
	ordered_bucket () = default;
	ordered_bucket (ordered_bucket&&) = default;
	ordered_bucket (const ordered_bucket&) = delete;
	ordered_bucket& operator = (ordered_bucket&&) = default;
	ordered_bucket& operator = (const ordered_bucket&) = delete;

	search_result search (const key_type& key)
	{
		auto result = binary_search (begin (_storage), end (_storage),
		                             key, std::less <key_type> {},
		                             by_key <key_type, value_type>);
		auto found = result.found;
		auto where = index_type {result.where};
		return {found, where};
	}

	value_type& insert (index_type where, key_type key, value_type value)
	// Precondition: search (key) = {false, where}
	{
		auto iter = _storage.emplace (where.iter, std::move (key), std::move (value));
		return iter->value ();
	}

	value_type& access (index_type where)
	// Precondition: where ≠ end (_storage)
	{
		return where.iter->value ();
	}
};

#endif
