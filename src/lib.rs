const NO_CHILDS: usize = std::usize::MAX;

const PASSABLE: usize = std::usize::MAX;
const SOURCE: usize = std::usize::MAX - 1;

const BACKTRACK: usize = 1 << 31;

#[no_mangle]
pub unsafe extern "C" fn min_cut_highest(
    node_count: usize, node_arr: *mut usize,
    edge_count: usize, edge_arr: *mut usize,
    source_count: usize, source_arr: *mut usize,
    sink_count: usize, sink_arr: *mut usize,
    result: *mut *const usize,
) -> usize {
    let nodes = Vec::from_raw_parts(node_arr, node_count, node_count);
    let edges = Vec::from_raw_parts(edge_arr, edge_count, edge_count);
    let sources = Vec::from_raw_parts(source_arr, source_count, source_count);
    let sinks = Vec::from_raw_parts(sink_arr, sink_count, sink_count);

    let mut sink_flags = vec![false; node_count];
    for &i in &sinks { sink_flags[i] = true; }
    let sink_flags = sink_flags;

    let mut residual_graph = vec![PASSABLE; node_count];

    loop {
        let mut visited = vec![false; node_count];
        let mut dfs_stack: Vec<usize> = sources.clone();

        while let Some(iref) = dfs_stack.last_mut() {
            let i = *iref;

            if i & BACKTRACK != 0 || visited[i] {
                dfs_stack.pop();
                continue;
            }
            visited[i] = true;

            let prev = residual_graph[i];
            let i = match prev {
                SOURCE => { dfs_stack.pop(); continue; },
                PASSABLE => {
                    *iref = i | BACKTRACK;
                    if sink_flags[i] { break; }
                    i
                },
                _ => {
                    *iref = i | BACKTRACK;
                    dfs_stack.push(prev);
                    dfs_stack.push(prev | BACKTRACK);
                    prev
                }
            };

            let ebeg = nodes[i];
            let eend = nodes[i + 1];
            if edges[ebeg] != NO_CHILDS {
                for j in ebeg..eend {
                    dfs_stack.push(edges[j]);
                }
            }
        }

        let mut it = dfs_stack.into_iter().filter(|x| x & BACKTRACK != 0).map(|x| x & !BACKTRACK);
        let mut bef = match it.next() {
            None => break,
            Some(bef) => bef,
        };
        residual_graph[bef] = SOURCE;

        for i in it {
            if i < bef {
                residual_graph[i] = bef;
            }
            else if residual_graph[bef] == i {
                residual_graph[bef] = PASSABLE;
            }
            bef = i;
        }
    }
    let residual_graph = residual_graph;

    let mut visited = vec![false; node_count];
    {
        let mut dfs_stack: Vec<usize> = sources.clone();

        while let Some(i) = dfs_stack.pop() {
            if visited[i] {
                continue;
            }
            visited[i] = true;

            let prev = residual_graph[i];
            let i = match prev {
                SOURCE => { continue; },
                PASSABLE => { if sink_flags[i] { continue }; i },
                _ => { dfs_stack.push(prev); prev }
            };

            let ebeg = nodes[i];
            let eend = nodes[i + 1];
            if edges[ebeg] != NO_CHILDS {
                for j in ebeg..eend {
                    dfs_stack.push(edges[j])
                }
            }
        }
    }
    let visited = visited;

    let mut cut: Vec<usize> = Vec::new();
    for i in 0..node_count - 1 {  // the last node is only a backstop
        if !visited[i] { continue }
        if sink_flags[i] { cut.push(i); continue }

        let ebeg = nodes[i];
        let eend = nodes[i + 1];
        if edges[ebeg] != NO_CHILDS {
            for j in ebeg..eend {
                if !visited[edges[j]] {
                    cut.push(i);
                    break;
                }
            }
        }
    }

    *result = cut.as_ptr();
    let cut_len = cut.len();

    std::mem::forget(cut);
    std::mem::forget(nodes);
    std::mem::forget(edges);
    std::mem::forget(sources);
    std::mem::forget(sinks);

    cut_len
}

#[no_mangle]
pub unsafe extern "C" fn free_min_cut_highest(result: *mut usize) {
    Box::from_raw(result);
}
